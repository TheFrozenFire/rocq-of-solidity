// SPDX-License-Identifier: GPL-3.0
pragma solidity >=0.0;

// Regression test for std::length_error in Object::toRocq.
//
// The Yul-side Object name for this contract is the contract name plus an
// id and an optional `_deployed` suffix. When the resulting bytes exceed
// 32, the prior padding computed [64 - hex_name.size()] as size_t which
// underflowed and asked std::string for a multi-petabyte allocation,
// surfacing as `std::length_error` at the user.
//
// The contract name below is 30 characters; with the `_NN_deployed`
// subobject suffix the Yul Object name is 42+ characters = 84+ hex
// characters, which triggers the bug on the broken code.
contract NameThatTriggersBugInRocqPad {
    uint256 x;
    function set(uint256 v) external { x = v; }
}
