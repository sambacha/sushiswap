/*
 * This is a specification file for MasterChefV2's formal verification
 * using the Certora prover.
 *
 * Run this file with scripts/run.sh
 */

// Declaration of contracts used in the sepc 
using DummyERC20A as tokenA
using DummyWeth as wethTokenImpl
using SymbolicStrategy as strategyInstance
using Borrower as borrower

/*
 * Declaration of methods that are used in the rules.
 * envfree indicate that the method is not dependent on the environment (msg.value, msg.sender).
 * Methods that are not declared here are assumed to be dependent on env.
 */
 
methods {
	// Getters for the internals
	userInfoAmount(uint256 pid, address user) returns (uint256) envfree 
	userInfoRewardDebt(uint256 pid, address user) returns (int256) envfree 

	//ERC20 
	balanceOf(address) => DISPATCHER(true) 
	totalSupply() => DISPATCHER(true)
	transferFrom(address from, address to, uint256 amount) => DISPATCHER(true)
	transfer(address to, uint256 amount) => DISPATCHER(true)
}

// Invariants

// In progess ...

// Rules

// rule sanity(method f) {
// 	env e;
// 	calldataarg args;
// 	f(e, args);
// 	assert(false);
// }

// Just testing. In progress ...
rule noChangeToOtherUsersAmount(method f, uint256 pid, address user) {
	env e;

	require user != msg.sender;

	uint256 _userInfoAmount = userInfoAmount(pid, user);

	calldataarg args;
	f(e, args);

	uint256 userInfoAmount_ = userInfoAmount(pid, user);

	assert(_userInfoAmount == userInfoAmount_, "user amount changed");
}

// rule noChangeToOtherUsersRewardDebt() {
	
// }
