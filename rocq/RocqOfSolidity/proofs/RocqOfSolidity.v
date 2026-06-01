Require Import RocqOfSolidity.RocqOfSolidity.
Require Import simulations.RocqOfSolidity.
Require coqutil.Datatypes.List.

Import RunO.

Module Memory.
  Definition of_u256_list (words : list U256.t) : Memory.t.
  Admitted.

  Lemma run_mload codes environment state
      (words : list U256.t) (index : nat) (word : U256.t) :
    List.nth_error words index = Some word ->
    state.(State.memory) = of_u256_list words ->
    {{? codes, environment, Some state |
      Stdlib.mload (32 * Z.of_nat index) ⇓
      Result.Ok word
    | Some state ?}}.
  Proof.
  Admitted.

  Lemma run_mstore codes environment state
      (words : list U256.t) (index : nat) (word : U256.t) :
    match List.update_nth words index word with
    | Some words' =>
      let state' := state <| State.memory := of_u256_list words' |> in
      {{? codes, environment, Some state |
        Stdlib.mstore (32 * Z.of_nat index) word ⇓
        Result.Ok tt
      | Some state' ?}}
    | None => True
    end.
  Proof.
  Admitted.

  Lemma update_at (index : nat) (word2 : U256.t)
      {A : Set} codes environment state1 e (output : A) state'
      (words1 : list U256.t) (word1 : U256.t)
      (H_word : word2 = word1)
      (H_nth : List.nth_error words1 index = Some word1)
      (H_memory : state1.(State.memory) = of_u256_list words1) :
    let state2 :=
      state1 <| State.memory := of_u256_list (List.replace_nth index words1 word2) |> in
    {{? codes, environment, Some state2 |
      e ⇓ output
    | state' ?}} ->
    {{? codes, environment, Some state1 |
      e ⇓ output
    | state' ?}}.
  Proof.
    intros.
    assert (state1 = state2). {
      unfold state2.
      replace (of_u256_list _) with state1.(State.memory). 2: {
        rewrite H_memory, H_word.
        f_equal.
        revert H_nth; clear; intros.
        revert index H_nth.
        induction words1; hauto lq: on.
      }
      sfirstorder.
    }
    congruence.
  Qed.
End Memory.

Module SimulatedMemory.
  Definition t : Set :=
    list U256.t.

  Definition init : t :=
    [0; 0; 0; 0; 0].
End SimulatedMemory.

Module Address.
  Lemma implies_and_mask address :
    Address.Valid.t address ->
    address = Z.land address (2 ^ 160 - 1).
  Proof.
  Admitted.
End Address.

(** A value that admits a direct representation on the storage. *)
Module StorableValue.
  (** For now the maps can only contain integers. *)
  Inductive t : Set :=
  | U256 (value : U256.t)
  | Map (value : Dict.t U256.t U256.t)
  | Map2 (value : Dict.t (U256.t * U256.t) U256.t)
  (** A mapping from a key to a packed struct of [uint256] fields. The
      Solidity storage layout is
      [keccak256(key, baseSlot) + field_offset], which differs from
      [Map2]'s nested-keccak shape. We reuse the same carrier as [Map2]
      so [map_get_u256] works, but distinguish via a new constructor
      so the sload-slot pattern can be matched precisely.
      The key shape is [(account, field_offset)]. *)
  | MapStruct (value : Dict.t (U256.t * U256.t) U256.t)
  (** A mapping from a key to a Solidity dynamic array (e.g.
      [mapping(K => T[])]). Solidity lays out the array data using its
      standard dynamic-array convention, but ANCHORED at
      [keccak256(key, baseSlot)] rather than at a fixed slot:

        slot[keccak(key, baseSlot)]                = array length
        slot[keccak(keccak(key, baseSlot)) + i]    = values[i]

      (Anchor uses the nested-keccak shape of a [mapping(K => _)] base,
      then the body uses a SINGLE-input keccak on the anchor to derive
      the data area -- same as a non-mapped dynamic array would do from
      its base slot.)

      The carrier is a [Dict.t U256.t (list U256.t)]: keys are the map
      keys (e.g. role bytes32), values are the per-key dynamic-array
      contents as a Coq list. Missing keys default to the empty list
      via [Dict.get] = None -> []. This is the honest framework
      primitive modelling OZ's [EnumerableSet] storage shape (and any
      other [mapping(K => T[])] consumer); the four sload/sstore
      lemmas below are written at the exact OZ-actual slot expressions
      so callers can compose without a per-contract trust axiom for
      the array shape. *)
  | MapToArray (value : Dict.t U256.t (list U256.t)).

  (** Default-zero lookup of an array body element. Out-of-range
      indices yield 0 (Solidity's implicit zero-init for unassigned
      array slots). *)
  Definition array_get_u256
      (map : Dict.t U256.t (list U256.t))
      (key : U256.t) (idx : nat) : U256.t :=
    match Dict.get map key with
    | Some lst => List.nth_default 0 lst idx
    | None => 0
    end.

  (** Default-zero lookup of an array length. Missing keys -> 0. *)
  Definition array_length_u256
      (map : Dict.t U256.t (list U256.t))
      (key : U256.t) : U256.t :=
    match Dict.get map key with
    | Some lst => Z.of_nat (List.length lst)
    | None => 0
    end.

  (** Set [arr[key][idx] := value]. If [key] is missing or the inner
      list is too short, the operation is a no-op (the lemma below is
      stated under a guard hypothesis that the index is in range). *)
  Definition array_assign_u256
      (map : Dict.t U256.t (list U256.t))
      (key : U256.t) (idx : nat) (value : U256.t) :
      Dict.t U256.t (list U256.t) :=
    let cur := match Dict.get map key with
               | Some lst => lst
               | None => []
               end in
    match List.update_nth cur idx value with
    | Some lst' => Dict.declare_or_assign map key lst'
    | None => map
    end.

  (** Set [arr[key]] length to [new_len]. Extends with zero or
      truncates to the requested length. Matches Solidity's
      length-write semantics (a write that grows the array zero-fills
      the new positions; a write that shrinks truncates and zeroes the
      dropped slots). *)
  Definition array_resize_u256
      (map : Dict.t U256.t (list U256.t))
      (key : U256.t) (new_len : nat) :
      Dict.t U256.t (list U256.t) :=
    let cur := match Dict.get map key with
               | Some lst => lst
               | None => []
               end in
    let cur_len := List.length cur in
    let resized :=
      if Nat.leb new_len cur_len then
        List.firstn new_len cur
      else
        cur ++ List.repeat (0 : U256.t) (new_len - cur_len)
    in
    Dict.declare_or_assign map key resized.

  (** The default value is zero when a key is not yet assigned. *)
  Definition map_get_u256 {K : Set} `{Dict.Eq.C K}
      (map : Dict.t K U256.t) (key : K) : U256.t :=
    match Dict.get map key with
    | Some value => value
    | None => 0
    end.

  Lemma map_get_u256_is_valid {K : Set} `{Dict.Eq.C K} (P_K : K -> Prop)
      (map : Dict.t K U256.t) (key : K)
      (H_map : Dict.Valid.t P_K U256.Valid.t map) :
    U256.Valid.t (map_get_u256 map key).
  Proof.
    unfold map_get_u256.
    pose proof (Dict.get_is_valid _ _ _ key H_map).
    destruct Dict.get; unfold U256.Valid.t in *; lia.
  Qed.
End StorableValue.

Module IsStorable.
  Class C (A : Set) : Set := {
    to_storable_value : A -> StorableValue.t;
  }.

  Global Instance IU256 : C U256.t := {
    to_storable_value := StorableValue.U256;
  }.

  Global Instance IMap : C (Dict.t U256.t U256.t) := {
    to_storable_value := StorableValue.Map;
  }.

  Global Instance IMap2 : C (Dict.t (U256.t * U256.t) U256.t) := {
    to_storable_value := StorableValue.Map2;
  }.

  Global Instance IMapToArray : C (Dict.t U256.t (list U256.t)) := {
    to_storable_value := StorableValue.MapToArray;
  }.
End IsStorable.

Module State.
  Definition get_current_storage
      (environment : Environment.t) (state : State.t) :
      option Storage.t :=
    let address := environment.(Environment.address) in
    let account := Dict.get state.(State.accounts) address in
    match account with
    | None => None
    | Some account => Some account.(Account.storage)
    end.

  Definition with_current_storage
      (environment : Environment.t) (state : State.t) (storage : Storage.t) :
      State.t :=
    let address := environment.(Environment.address) in
    let accounts :=
      Dict.assign_function state.(State.accounts) address (fun account =>
        account <| Account.storage := storage |>
      ) in
    match accounts with
    | None => state
    | Some accounts => state <| State.accounts := accounts |>
    end.

  Lemma get_current_storage_with_current_storage_eq
      environment state storage :
    get_current_storage environment (with_current_storage environment state storage) =
    Some storage.
  Proof.
  Admitted.
End State.
Global Opaque State.get_current_storage State.with_current_storage.

Lemma run_keccak256_tuple2 codes environment state
    (memory : list U256.t) (index : nat) (a b : U256.t) :
  state.(State.memory) = Memory.of_u256_list memory ->
  List.nth_error memory index = Some a ->
  List.nth_error memory (S index) = Some b ->
  {{? codes, environment, Some state |
    Stdlib.keccak256 (32 * (Z.of_nat index)) (32 * 2) ⇓
    Result.Ok (keccak256_tuple2 a b)
  | Some state ?}}.
Proof.
Admitted.

(** ----- Single-word keccak -----

    Solidity's [EnumerableSet] (and any dynamic-array layout that
    derives its data slot from the array's anchor) lowers to
    [mstore(0, anchor); keccak256(0, 0x20)] -- a SINGLE-input keccak.
    [run_keccak256_single] is the proof-side counterpart to
    [keccak256_single] in [simulations/RocqOfSolidity.v]: given a
    memory layout where word [index] holds [a], stepping
    [Stdlib.keccak256 (32 * index) 32] produces [keccak256_single a].

    The slot-expression shape that consumes the result is
    [keccak256_single anchor + offset]; sload / sstore axioms at that
    shape are written downstream of this primitive (they are not
    one-size-fits-all because the storage projection a caller uses
    for the array body varies -- direct [Dict.t U256.t U256.t] keyed
    by offset, or [Dict.t (U256.t * U256.t) U256.t] keyed by
    [(anchor, offset)], or a per-caller bridge to a multi-role
    [Map2]). Callers add the matching sload/sstore axiom alongside
    their per-contract storage projection. *)
Lemma run_keccak256_single codes environment state
    (memory : list U256.t) (index : nat) (a : U256.t) :
  state.(State.memory) = Memory.of_u256_list memory ->
  List.nth_error memory index = Some a ->
  {{? codes, environment, Some state |
    Stdlib.keccak256 (32 * (Z.of_nat index)) 32 ⇓
    Result.Ok (keccak256_single a)
  | Some state ?}}.
Proof.
Admitted.

Module Storage.
  Definition of_storable_values (values : list StorableValue.t) : Storage.t.
  Admitted.

  Lemma run_sload_u256
      (values : list StorableValue.t)
      (index : nat)
      (value : U256.t)
      codes environment state :
    State.get_current_storage environment state = Some (of_storable_values values) ->
    List.nth_error values index = Some (StorableValue.U256 value) ->
    {{? codes, environment, Some state |
      Stdlib.sload (Z.of_nat index) ⇓
      Result.Ok value
    | Some state ?}}.
  Proof.
  Admitted.

  Lemma run_sstore_u256
      (values : list StorableValue.t)
      (index : nat)
      (value : U256.t)
      codes environment state :
    let state := State.with_current_storage environment state (of_storable_values values) in
    match List.update_nth values index (StorableValue.U256 value) with
    | Some values' =>
      let state' := State.with_current_storage environment state (of_storable_values values') in
      {{? codes, environment, Some state |
        Stdlib.sstore (Z.of_nat index) value ⇓
        Result.Ok tt
      | Some state' ?}}
    | None => True
    end.
  Proof.
  Admitted.

  Lemma run_sload_map_u256
      (values : list StorableValue.t)
      (index : nat)
      (map : Dict.t U256.t U256.t)
      (key : U256.t)
      codes environment state :
    List.nth_error values index = Some (StorableValue.Map map) ->
    {{? codes, environment, state |
      Stdlib.sload (keccak256_tuple2 key (Z.of_nat index)) ⇓
      Result.Ok (StorableValue.map_get_u256 map key)
    | state ?}}.
  Proof.
  Admitted.

  Lemma run_sstore_map_u256
      (values : list StorableValue.t)
      (index : nat)
      (key : U256.t) (value : U256.t)
      codes environment state :
    State.get_current_storage environment state = Some (of_storable_values values) ->
    match List.nth_error values index with
    | Some (StorableValue.Map map) =>
      let map' := Dict.declare_or_assign map key value in
      match List.update_nth values index (StorableValue.Map map') with
      | Some values' =>
        let state' := State.with_current_storage environment state (of_storable_values values') in
        {{? codes, environment, Some state |
          Stdlib.sstore (keccak256_tuple2 key (Z.of_nat index)) value ⇓
          Result.Ok tt
        | Some state' ?}}
      | None => True
      end
    | _ => True
    end.
  Proof.
  Admitted.

  Lemma run_sload_map2_u256
      (values : list StorableValue.t)
      (index : nat)
      (map : Dict.t (U256.t * U256.t) U256.t)
      (key1 key2 : U256.t)
      codes environment state :
    List.nth_error values index = Some (StorableValue.Map2 map) ->
    {{? codes, environment, state |
      Stdlib.sload (keccak256_tuple2 key2 (keccak256_tuple2 key1 (Z.of_nat index))) ⇓
      Result.Ok (StorableValue.map_get_u256 map (key1, key2))
    | state ?}}.
  Proof.
  Admitted.

  Lemma run_sstore_map2_u256
      (values : list StorableValue.t)
      (index : nat)
      (key1 key2 : U256.t) (value : U256.t)
      codes environment state :
    State.get_current_storage environment state = Some (of_storable_values values) ->
    match List.nth_error values index with
    | Some (StorableValue.Map2 map) =>
      let map' := Dict.declare_or_assign map (key1, key2) value in
      match List.update_nth values index (StorableValue.Map2 map') with
      | Some values' =>
        let state' := State.with_current_storage environment state (of_storable_values values') in
        {{? codes, environment, Some state |
          Stdlib.sstore
            (keccak256_tuple2 key2 (keccak256_tuple2 key1 (Z.of_nat index))) value ⇓
          Result.Ok tt
        | Some state' ?}}
      | None => True
      end
    | _ => True
    end.
  Proof.
  Admitted.

  (** ----- MapStruct: [mapping(K => struct { f0; f1; ... })] -----

      The Solidity storage layout for [mapping(K => Struct)] places
      field [offset] of [Struct] at slot
      [keccak256(key, baseSlot) + Z.of_nat offset]. We expose two
      lemmas matching that exact slot expression. *)

  Lemma run_sload_struct_field
      (values : list StorableValue.t)
      (index : nat)
      (map : Dict.t (U256.t * U256.t) U256.t)
      (key : U256.t) (offset : U256.t)
      codes environment state :
    List.nth_error values index = Some (StorableValue.MapStruct map) ->
    {{? codes, environment, state |
      Stdlib.sload (keccak256_tuple2 key (Z.of_nat index) + offset) ⇓
      Result.Ok (StorableValue.map_get_u256 map (key, offset))
    | state ?}}.
  Proof.
  Admitted.

  Lemma run_sstore_struct_field
      (values : list StorableValue.t)
      (index : nat)
      (key : U256.t) (offset : U256.t) (value : U256.t)
      codes environment state :
    State.get_current_storage environment state = Some (of_storable_values values) ->
    match List.nth_error values index with
    | Some (StorableValue.MapStruct map) =>
      let map' := Dict.declare_or_assign map (key, offset) value in
      match List.update_nth values index (StorableValue.MapStruct map') with
      | Some values' =>
        let state' := State.with_current_storage environment state (of_storable_values values') in
        {{? codes, environment, Some state |
          Stdlib.sstore (keccak256_tuple2 key (Z.of_nat index) + offset) value ⇓
          Result.Ok tt
        | Some state' ?}}
      | None => True
      end
    | _ => True
    end.
  Proof.
  Admitted.

  (** ----- MapToArray: [mapping(K => T[])] -----

      Honest framework primitive for the OZ [EnumerableSet] storage
      shape (and any other [mapping(K => T[])] consumer). The four
      lemmas below match the EXACT slot expressions that solc emits
      for such a mapping anchored at slot [index]:

        - length:   sload (keccak(key, index))           => Z.of_nat (length arr[key])
        - body[i]:  sload (keccak(keccak(key, index)) + i) => arr[key][i]

      Each is the [MapToArray] analogue of the [Map] / [Map2] /
      [MapStruct] lemmas above. They are [Admitted] in the framework
      (same shape as the other Storage primitives) -- the trust
      transfers to one common audit obligation rather than to
      per-contract slot-shape axioms. *)

  Lemma run_sload_maptoarray_length
      (values : list StorableValue.t)
      (index : nat)
      (map : Dict.t U256.t (list U256.t))
      (key : U256.t)
      codes environment state :
    List.nth_error values index = Some (StorableValue.MapToArray map) ->
    {{? codes, environment, state |
      Stdlib.sload (keccak256_tuple2 key (Z.of_nat index)) ⇓
      Result.Ok (StorableValue.array_length_u256 map key)
    | state ?}}.
  Proof.
  Admitted.

  Lemma run_sload_maptoarray_elem
      (values : list StorableValue.t)
      (index : nat)
      (map : Dict.t U256.t (list U256.t))
      (key : U256.t) (i : nat)
      codes environment state :
    List.nth_error values index = Some (StorableValue.MapToArray map) ->
    {{? codes, environment, state |
      Stdlib.sload (keccak256_single (keccak256_tuple2 key (Z.of_nat index)) + Z.of_nat i) ⇓
      Result.Ok (StorableValue.array_get_u256 map key i)
    | state ?}}.
  Proof.
  Admitted.

  Lemma run_sstore_maptoarray_length
      (values : list StorableValue.t)
      (index : nat)
      (key : U256.t) (new_len : nat)
      codes environment state :
    State.get_current_storage environment state = Some (of_storable_values values) ->
    match List.nth_error values index with
    | Some (StorableValue.MapToArray map) =>
      let map' := StorableValue.array_resize_u256 map key new_len in
      match List.update_nth values index (StorableValue.MapToArray map') with
      | Some values' =>
        let state' := State.with_current_storage environment state (of_storable_values values') in
        {{? codes, environment, Some state |
          Stdlib.sstore (keccak256_tuple2 key (Z.of_nat index)) (Z.of_nat new_len) ⇓
          Result.Ok tt
        | Some state' ?}}
      | None => True
      end
    | _ => True
    end.
  Proof.
  Admitted.

  Lemma run_sstore_maptoarray_elem
      (values : list StorableValue.t)
      (index : nat)
      (key : U256.t) (i : nat) (value : U256.t)
      codes environment state :
    State.get_current_storage environment state = Some (of_storable_values values) ->
    match List.nth_error values index with
    | Some (StorableValue.MapToArray map) =>
      let map' := StorableValue.array_assign_u256 map key i value in
      match List.update_nth values index (StorableValue.MapToArray map') with
      | Some values' =>
        let state' := State.with_current_storage environment state (of_storable_values values') in
        {{? codes, environment, Some state |
          Stdlib.sstore (keccak256_single (keccak256_tuple2 key (Z.of_nat index)) + Z.of_nat i) value ⇓
          Result.Ok tt
        | Some state' ?}}
      | None => True
      end
    | _ => True
    end.
  Proof.
  Admitted.
End Storage.

Module SimulatedStorage.
  Definition t : Set :=
    list StorableValue.t.

  Definition init : t := [
    StorableValue.Map [];
    StorableValue.Map [];
    StorableValue.U256 0
  ].
End SimulatedStorage.

Definition make_state environment state
    (memory : SimulatedMemory.t) (storage : SimulatedStorage.t) :
    State.t :=
  State.with_current_storage environment
    (state <| State.memory := Memory.of_u256_list memory |>)
    (Storage.of_storable_values storage).

Lemma get_memory_make_state_eq environment state
    memory storage :
  (make_state environment state memory storage).(State.memory) =
  Memory.of_u256_list memory.
Proof.
Admitted.

(** Lemma to put the state always in the same form. *)
Module CanonizeState.
  Lemma update_memory_eq environment state
      memory storage new_memory :
    (make_state environment state memory storage) <|
      State.memory := Memory.of_u256_list new_memory
    |> =
    make_state environment state new_memory storage.
  Proof.
  Admitted.

  Lemma update_storage_eq environment state
        memory storage new_storage :
    State.with_current_storage environment
      (make_state environment state memory storage)
      (Storage.of_storable_values new_storage) =
    make_state environment state memory new_storage.
  Proof.
  Admitted.

  Lemma with_current_storage_twice_eq environment state
      storage1 storage2 :
    State.with_current_storage environment
      (State.with_current_storage environment state storage1)
      storage2 =
    State.with_current_storage environment state storage2.
  Proof.
  Admitted.

  Ltac execute := repeat (
    rewrite update_memory_eq ||
    rewrite update_storage_eq ||
    rewrite with_current_storage_twice_eq ||
    match goal with
    | |- context[
      State.with_current_storage ?environment
        (?state <|State.memory:= Memory.of_u256_list ?memory |>)
        (Storage.of_storable_values ?storage)
      ] => fold (make_state environment state memory storage)
    end
  ).
End CanonizeState.

Ltac apply_run_mload :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ ?memory _) | Stdlib.mload ?offset ⇓ _ | _ ?}} =>
    eapply (Memory.run_mload _ _ _ memory (Z.to_nat (offset / 32)));
    try reflexivity;
    try apply get_memory_make_state_eq
  end.

Ltac apply_run_mstore :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ ?memory _) | Stdlib.mstore ?offset ?value ⇓ _ | _ ?}} =>
    apply (Memory.run_mstore _ _ _ memory (Z.to_nat (offset / 32)) value)
  end.

Ltac apply_memory_update_at index word2 :=
  let index := eval cbv in (Z.to_nat (index / 32)) in
  eapply (Memory.update_at index word2);
    try apply get_memory_make_state_eq;
    [|reflexivity|];
    unfold List.replace_nth;
    CanonizeState.execute.

Ltac apply_run_sload_u256 :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) | Stdlib.sload ?slot ⇓ _ | _ ?}} =>
    apply (Storage.run_sload_u256 storage (Z.to_nat slot));
    try reflexivity;
    try apply State.get_current_storage_with_current_storage_eq
  end.

Ltac apply_run_sstore_u256 :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) | Stdlib.sstore ?slot ?value ⇓ _ | _ ?}} =>
    apply (Storage.run_sstore_u256 storage (Z.to_nat slot) value)
  end.

Ltac apply_run_sload_map_u256 :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sload (keccak256_tuple2 ?key ?index) ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sload_map_u256 storage (Z.to_nat index) _ key);
    try reflexivity
  end.

Ltac apply_run_sstore_map_u256 :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sstore (keccak256_tuple2 ?key ?index) ?value ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sstore_map_u256 storage (Z.to_nat index) key value);
    try reflexivity;
    try apply State.get_current_storage_with_current_storage_eq
  end.

Ltac apply_run_sload_map2_u256 :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sload (keccak256_tuple2 ?key2 (keccak256_tuple2 ?key1 ?index)) ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sload_map2_u256 storage (Z.to_nat index) _ key1 key2);
    try reflexivity
  end.

Ltac apply_run_sstore_map2_u256 :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sstore (keccak256_tuple2 ?key2 (keccak256_tuple2 ?key1 ?index)) ?value ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sstore_map2_u256 storage (Z.to_nat index) key1 key2 value);
    try reflexivity;
    try apply State.get_current_storage_with_current_storage_eq
  end.

Ltac apply_run_sload_struct_field :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sload (keccak256_tuple2 ?key ?index + ?offset) ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sload_struct_field storage (Z.to_nat index) _ key offset);
    try reflexivity
  end.

Ltac apply_run_sstore_struct_field :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sstore (keccak256_tuple2 ?key ?index + ?offset) ?value ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sstore_struct_field storage (Z.to_nat index) key offset value);
    try reflexivity;
    try apply State.get_current_storage_with_current_storage_eq
  end.

(** ----- MapToArray Ltacs ----- *)

Ltac apply_run_sload_maptoarray_length :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sload (keccak256_tuple2 ?key ?index) ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sload_maptoarray_length storage (Z.to_nat index) _ key);
    try reflexivity
  end.

Ltac apply_run_sload_maptoarray_elem :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sload (keccak256_single (keccak256_tuple2 ?key ?index) + ?i) ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sload_maptoarray_elem storage (Z.to_nat index) _ key (Z.to_nat i));
    try reflexivity
  end.

Ltac apply_run_sstore_maptoarray_length :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sstore (keccak256_tuple2 ?key ?index) ?new_len ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sstore_maptoarray_length storage (Z.to_nat index) key (Z.to_nat new_len));
    try reflexivity;
    try apply State.get_current_storage_with_current_storage_eq
  end.

Ltac apply_run_sstore_maptoarray_elem :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ _ ?storage) |
      Stdlib.sstore (keccak256_single (keccak256_tuple2 ?key ?index) + ?i) ?value ⇓ _
    | _ ?}} =>
    eapply (Storage.run_sstore_maptoarray_elem storage (Z.to_nat index) key (Z.to_nat i) value);
    try reflexivity;
    try apply State.get_current_storage_with_current_storage_eq
  end.

Ltac apply_run_keccak256_tuple2 :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ ?memory _) | Stdlib.keccak256 ?pointer 64 ⇓ _ | _ ?}} =>
    apply (run_keccak256_tuple2 _ _ _ memory (Z.to_nat (pointer / 32)));
    try reflexivity;
    try apply get_memory_make_state_eq
  end.

Ltac apply_run_keccak256_single :=
  match goal with
  | |- {{? _, _, Some (make_state _ _ ?memory _) | Stdlib.keccak256 ?pointer 32 ⇓ _ | _ ?}} =>
    apply (run_keccak256_single _ _ _ memory (Z.to_nat (pointer / 32)));
    try reflexivity;
    try apply get_memory_make_state_eq
  end.
