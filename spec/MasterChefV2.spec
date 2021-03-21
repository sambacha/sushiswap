/*
 * This is a specification file for MasterChefV2's formal verification
 * using the Certora prover.
 *
 * Run this file with scripts/_runMasterChefV2.sh
 */

// Declaration of contracts used in the sepc 
using DummyERC20A as tokenA
using DummyWeth as wethTokenImpl
using SymbolicStrategy as strategyInstance
using Borrower as borrower
using RewarderMock as rewarderMock

/*
 * Declaration of methods that are used in the rules.
 * envfree indicate that the method is not dependent on the environment (msg.value, msg.sender).
 * Methods that are not declared here are assumed to be dependent on env.
 */
methods {
	// Getters for the internals
	userInfoAmount(uint256 pid, address user) returns (uint256) envfree 
	userInfoRewardDebt(uint256 pid, address user) returns (int256) envfree 
	userLpTokenBalanceOf(uint256 pid, address user) returns (uint256) envfree 

	sushiBalanceOf(address user) returns (uint256) envfree 

	poolInfoAccSushiPerShare(uint256 pid) returns (uint128) envfree
	poolInfoLastRewardBlock(uint256 pid) returns (uint64) envfree
	poolInfoAllocPoint(uint256 pid) returns (uint64) envfree

	// ERC20 
	balanceOf(address) => DISPATCHER(true) 
	totalSupply() => DISPATCHER(true)
	transferFrom(address from, address to, uint256 amount) => DISPATCHER(true)
	transfer(address to, uint256 amount) => DISPATCHER(true)

	// General Helpers
	compare(int256 x, int256 y) returns (bool) envfree // Helper for int operations
	intEquality(int256 x, int256 y) returns (bool) envfree // Helper for to check int equality

	// Helper Invariant Functions
	poolLength() returns (uint256) envfree
	lpTokenLength() returns (uint256) envfree
	rewarderLength() returns (uint256) envfree
	pidToAddressOfLpToken(uint256 pid) returns (address) envfree
	pidToAddressOfRewarder(uint256 pid) returns (address) envfree
}

// Constants

definition MAX_UINT256() returns uint256 =
	0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

// Invariants

invariant existanceOfPid(uint256 pid, address user)
	(pidToAddressOfLpToken(pid) == 0) => (poolInfoAllocPoint(pid) == 0 && userInfoAmount(pid, user) == 0 && pidToAddressOfRewarder(pid) == 0)

// the userInfo map size should also be equal? (can't get the size of mapping in solidity)
invariant integrityOfLength() 
	poolLength() == lpTokenLength() && lpTokenLength() == rewarderLength()

// It is not possible to compare IRC20 since they are not primitive types, how can I compare them?
// Are they just addresses? If not, can I compare their addresses? If yes, How do I get their addresses? (Can probably cast to an address)
invariant singularLpToken(uint256 pid1, uint256 pid2)
	(pidToAddressOfLpToken(pid1) == pidToAddressOfLpToken(pid2)) => (pid1 == pid2)

// Invariants as Rules

// failing because of updatePool from lines 170 - 174, I don't understand what's wrong.
// I looked carefully, but seems fine to me. Ask Nurit to take a look.
// I don't understand what it means by op is also different block.
rule monotonicityOfAccSushiPerShare(uint256 pid, method f) {
	env e;

	uint128 _poolInfoAccSushiPerShare = poolInfoAccSushiPerShare(pid);

	calldataarg args;
	f(e, args);

	uint128 poolInfoAccSushiPerShare_ = poolInfoAccSushiPerShare(pid);

	assert(poolInfoAccSushiPerShare_ >= _poolInfoAccSushiPerShare, 
		   "poolInfo accSushiPerShare not monotonic");
}

rule monotonicityOfLastRewardBlock(uint256 pid, method f) {
	env e;

	uint64 _poolInfoLastRewardBlock = poolInfoLastRewardBlock(pid);

	calldataarg args;
	f(e, args);

	uint64 poolInfoLastRewardBlock_ = poolInfoLastRewardBlock(pid);

	assert(poolInfoLastRewardBlock_ >= _poolInfoLastRewardBlock, 
		   "poolInfo lastRewardBlock not monotonic");
}

// Rules

// rule sanity(method f) {
// 	env e;
// 	calldataarg args;
// 	f(e, args);
// 	assert(false);
// }

rule noChangeToOtherUsersAmount(method f, uint256 pid, uint256 amount,
								address other, address to) {
	env e;

	require other != e.msg.sender;

	uint256 _userInfoAmount = userInfoAmount(pid, other);

	if (f.selector == deposit(uint256, uint256, address).selector) {
		deposit(e, pid, amount, to);
	} else {
		calldataarg args;
		f(e, args);
	}

	uint256 userInfoAmount_ = userInfoAmount(pid, other);

	 // to should only be limited in deposit
	if (f.selector == deposit(uint256, uint256, address).selector && other == to) {
		assert(_userInfoAmount <= userInfoAmount_, "other's user amount changed");
	} else {
		assert(_userInfoAmount == userInfoAmount_, "other's user amount changed");
	}
}

// Failing on deposit, did some digging, but still not sure what's going on.
// rewardDebt is int256 not uint256, something might be there.
rule noChangeToOtherUsersRewardDebt(method f, uint256 pid, uint256 amount,
								address other, address to) {
	env e;

	require other != e.msg.sender;

	int256 _userInfoRewardDebt = userInfoRewardDebt(pid, other);

	if (f.selector == deposit(uint256, uint256, address).selector) {
		deposit(e, pid, amount, to);
	} else {
		calldataarg args;
		f(e, args);
	}

	int256 userInfoRewardDebt_ = userInfoRewardDebt(pid, other);

	// to should only be limited in deposit
	if (f.selector == deposit(uint256, uint256, address).selector && other == to) {

		assert(compare(_userInfoRewardDebt, userInfoRewardDebt_), "other's user rewardDebt changed");
	} else {
		assert(_userInfoRewardDebt == userInfoRewardDebt_, "other's user rewardDebt changed");
	}
}

// rule noChangeToOtherPool(uint256 pid1, uint256 pid2) {

// }

// Very weird, not passing even on the simple case for deposit
rule preserveTotalAssetOfUser(method f, uint256 pid, address user,
					          address to, uint256 amount) {
	env e;

	require user == e.msg.sender && user == to;

	uint256 _totalUserAssets = userLpTokenBalanceOf(pid, user) + userInfoAmount(pid, user);

	if (f.selector == deposit(uint256, uint256, address).selector) {
		deposit(e, pid, amount, to);
	} else if (f.selector == withdraw(uint256, uint256, address).selector) {
		withdraw(e, pid, amount, to);
	} else if (f.selector == emergencyWithdraw(uint256, address).selector) {
		emergencyWithdraw(e, pid, to);
	} else {
		calldataarg args;
		f(e, args);
	}

	uint256 totalUserAssets_ = userLpTokenBalanceOf(pid, user) + userInfoAmount(pid, user);

	assert(_totalUserAssets == totalUserAssets_,
		   "total user balance is not preserved");
}

// Debugging version for preserveTotalAssetOfUser
// rule preserveTotalAssetOfUser(method f, uint256 pid, address user,
// 					          address to, uint256 amount) {
// 	env e;

// 	uint256 _userBalanceOf = userLpTokenBalanceOf(pid, e.msg.sender);
// 	uint256 _userInfoAmount = userInfoAmount(pid, e.msg.sender);

// 	if (f.selector == deposit(uint256, uint256, address).selector) {
// 		deposit(e, pid, amount, e.msg.sender);
// 	} else if (f.selector == withdraw(uint256, uint256, address).selector) {
// 		withdraw(e, pid, amount, e.msg.sender);
// 	} else if (f.selector == emergencyWithdraw(uint256, address).selector) {
// 		emergencyWithdraw(e, pid, e.msg.sender);
// 	} else {
// 		calldataarg args;
// 		f(e, args);
// 	}

// 	uint256 userBalanceOf_ = userLpTokenBalanceOf(pid, e.msg.sender);
// 	uint256 userInfoAmount_ = userInfoAmount(pid, e.msg.sender);

// 	assert((_userBalanceOf + _userInfoAmount) == (userBalanceOf_ + userInfoAmount_),
// 		   "total user balance is not preserved");
// }

// rule solvency() {

// }

rule correctEffectOfChangeToAllocPoint(uint256 pid, address user,
									   uint256 allocPoint, bool overwrite) {
	env e1;
	env e2;
	env e3;

	require e2.block.number >= e1.block.number;
	require e3.block.number >= e2.block.number;

	uint256 _pendingSushi = pendingSushi(e1, pid, user);

	set(e2, pid, allocPoint, rewarderMock, overwrite);

	uint256 pendingSushi_ = pendingSushi(e3, pid, user);

	assert(pendingSushi_ >= _pendingSushi, 
	       "The effect of changing allocPoint is incorrect");
}

// How to get the address of SUSHI? Or do I just need to use the harness?
rule sushiGivenInHarvestEqualsPendingSushi(uint256 pid, address user, address to) {
	env e;

	require to == user;

	uint256 userSushiBalance = sushiBalanceOf(user);
	uint256 userPendingSushi = pendingSushi(e, pid, user);

	// Does success return value matters? Check with Nurit
	harvest(e, pid, to);

	uint256 userSushiBalance_ = sushiBalanceOf(user);

	assert(userSushiBalance_ == (userSushiBalance + userPendingSushi),
		   "pending sushi not equal to the sushi given in harvest");
}

rule depositThenWithdraw(uint256 pid, address user, uint256 amount, address to) {
	env e;

	require e.msg.sender == to;

	uint256 _userInfoAmount = userInfoAmount(pid, user);
	int256 _userInfoRewardDebt = userInfoRewardDebt(pid, user);

	deposit(e, pid, amount, to);
	withdraw(e, pid, amount ,to);

	uint256 userInfoAmount_ = userInfoAmount(pid, user);
	int256 userInfoRewardDebt_ = userInfoRewardDebt(pid, user);

	assert(_userInfoAmount == userInfoAmount_, "user amount changed");
	assert(intEquality(_userInfoRewardDebt, userInfoRewardDebt_),
		   "user reward debt changed");
}

// rule depositThenWithdrawWithRevert() {
	
// }

// rule orderOfOpeerationWithdrawAndHarvest() {
// 	env e;
// 	storage initStorage = lastStorage;

// 	// call withdraw then harvest

// 	// store poolInfo1
// 	// store userInfo1

// 	// call harvest then withdraw at initStorage

// 	// store poolInfo2
// 	// store userInfo2

// 	// check for equality among poolInfo1 == poolInfo2, userInfo1 == userInfo2
// }

// Can combine the additivity of deposit and withdraw using a helper function
// Have them seperated just for now, once Nurit approves, combine them
rule additivityOfDepositOnAmount(uint256 pid, uint256 x, uint256 y, address to) {
	env e;
	storage initStorage = lastStorage;

	deposit(e, pid, x, to);
	deposit(e, pid, y, to);

	uint256 splitScenarioToAmount = userInfoAmount(pid, to);
	uint256 splitScenarioSenderBalanceOf = userLpTokenBalanceOf(pid, e.msg.sender);

	require x + y <= MAX_UINT256();
	uint256 sum = x + y;
	deposit(e, pid, sum, to) at initStorage;
	
	uint256 sumScenarioToAmount = userInfoAmount(pid, to);
	uint256 sumScenarioSenderBalanceOf = userLpTokenBalanceOf(pid, e.msg.sender);

	assert(splitScenarioToAmount == sumScenarioToAmount, 
		   "deposit is not additive on amount");

	assert(splitScenarioSenderBalanceOf == sumScenarioSenderBalanceOf, 
		   "deposit is not additive on amount");
}

rule additivityOfDepositOnRewardDebt(uint256 pid, uint256 x, uint256 y, address to) {
	env e;
	storage initStorage = lastStorage;

	deposit(e, pid, x, to);
	deposit(e, pid, y, to);

	int256 splitScenarioUserRewardDebt = userInfoRewardDebt(pid, to);

	require x + y <= MAX_UINT256();
	uint256 sum = x + y;
	deposit(e, pid, sum, to) at initStorage;
	
	int256 sumScenarioUserRewardDebt = userInfoRewardDebt(pid, to);

	assert(intEquality(splitScenarioUserRewardDebt, sumScenarioUserRewardDebt), 
		   "deposit is not additive on rewardDebt");
}

rule additivityOfWithdrawOnAmount(uint256 pid, uint256 x, uint256 y, address to) {
	env e;
	storage initStorage = lastStorage;

	withdraw(e, pid, x, to);
	withdraw(e, pid, y, to);

	uint256 splitScenarioSenderAmount = userInfoAmount(pid, e.msg.sender);
	uint256 splitScenarioToBalanceOf = userLpTokenBalanceOf(pid, to);

	require x + y <= MAX_UINT256();
	uint256 sum = x + y;
	withdraw(e, pid, sum, to) at initStorage;
	
	uint256 sumScenarioSenderAmount = userInfoAmount(pid, e.msg.sender);
	uint256 sumScenarioToBalanceOf = userLpTokenBalanceOf(pid, to);

	assert(splitScenarioSenderAmount == sumScenarioSenderAmount, 
		   "withdraw is not additive on amount");

	assert(splitScenarioToBalanceOf == sumScenarioToBalanceOf, 
		   "withdraw is not additive on amount");
}

rule additivityOfWithdrawOnRewardDebt(uint256 pid, uint256 x, uint256 y, address to) {
	env e;
	storage initStorage = lastStorage;

	withdraw(e, pid, x, to);
	withdraw(e, pid, y, to);

	int256 splitScenarioUserRewardDebt = userInfoRewardDebt(pid, to);

	require x + y <= MAX_UINT256();
	uint256 sum = x + y;
	withdraw(e, pid, sum, to) at initStorage;
	
	int256 sumScenarioUserRewardDebt = userInfoRewardDebt(pid, to);

	assert(intEquality(splitScenarioUserRewardDebt, sumScenarioUserRewardDebt), 
		   "withdraw is not additive on rewardDebt");
}