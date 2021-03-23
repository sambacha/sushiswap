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
using DummySUSHI as sushiToken

/*
 * Declaration of methods that are used in the rules.
 * envfree indicate that the method is not dependent on the environment (msg.value, msg.sender).
 * Methods that are not declared here are assumed to be dependent on env.
 */
methods {
	// Getters for the internals
	userInfoAmount(uint256 pid, address user) returns (uint256) envfree 
	userInfoRewardDebt(uint256 pid, address user) returns (int256) envfree 
	userLpTokenBalanceOf(uint256 pid, address user) returns (uint256) envfree // How to remove this? (Ask Nurit)

	poolInfoAccSushiPerShare(uint256 pid) returns (uint128) envfree
	poolInfoLastRewardBlock(uint256 pid) returns (uint64) envfree
	poolInfoAllocPoint(uint256 pid) returns (uint64) envfree

	lpToken(uint256 pid) returns (address) envfree
	rewarder(uint256 pid) returns (address) envfree

	// ERC20 
	balanceOf(address) => DISPATCHER(true) 
	totalSupply() => DISPATCHER(true)
	transferFrom(address from, address to, uint256 amount) => DISPATCHER(true)
	transfer(address to, uint256 amount) => DISPATCHER(true)
	approve(address t, uint256 amount) => NONDET
	permit(address owner, address spender, uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) => NONDET
	
	// General Helpers
	compare(int256 x, int256 y) returns (bool) envfree // Helper to check <= for int256
	intEquality(int256 x, int256 y) returns (bool) envfree // Helper to check int equality
	compareUint128(uint128 x, uint128 y) returns (bool) envfree // Helper to check >= for uint128
	intDeltaOne(int256 x, int256 y) returns (bool) envfree // Helper to allow a difference of 1 for int256

	// Helper Invariant Functions
	poolLength() returns (uint256) envfree
	lpTokenLength() returns (uint256) envfree
	rewarderLength() returns (uint256) envfree

	// SUSHI token
	SUSHI() returns (address) envfree
	sushiToken.balanceOf(address) returns (uint256)  

	// Rewarder
	//SIG_ON_SUSHI_REWARD = 0xbb6cc2ef; // onSushiReward(uint256,address,uint256)
	0xbb6cc2ef => NONDET

	// MasterChefV1
	deposit(uint256 pid, uint256 amount) => NONDET
}

// Constants

definition MAX_UINT256() returns uint256 =
	0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

// Invariants

invariant existenceOfPid(uint256 pid, address user)
	pid > lpTokenLength() || 
	(lpToken(pid) == 0) => (poolInfoAllocPoint(pid) == 0 && userInfoAmount(pid, user) == 0 && rewarder(pid) == 0)

invariant integrityOfLength() 
	poolLength() == lpTokenLength() && lpTokenLength() == rewarderLength()

invariant validityOfLpToken(uint256 pid, address user)
	(userInfoAmount(pid, user) > 0) => (lpToken(pid) != 0)

// TODO: (1)
// invariant integrityOfTotalAllocPoint()

// Invariants as Rules

rule monotonicityOfAccSushiPerShare(uint256 pid, method f) {
	env e;

	uint128 _poolInfoAccSushiPerShare = poolInfoAccSushiPerShare(pid);

	calldataarg args;
	f(e, args);

	uint128 poolInfoAccSushiPerShare_ = poolInfoAccSushiPerShare(pid);

	assert compareUint128(poolInfoAccSushiPerShare_, _poolInfoAccSushiPerShare);
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

rule noChangeToOtherPool(uint256 pid, uint256 otherPid) {
	require pid != otherPid;

	uint128 _otherAccSushiPerShare = poolInfoAccSushiPerShare(otherPid);
	uint64 _otherLastRewardBlock = poolInfoLastRewardBlock(otherPid);
	uint64 _otherAllocPoint = poolInfoAllocPoint(otherPid);

	method f;
	require f.selector != massUpdatePools(uint256[]).selector;

	uint256 allocPoint;
	bool overwrite;
	address user;
	uint256 amount;

	callFunctionWithParams(f, pid, allocPoint, overwrite, user, amount);

	uint128 otherAccSushiPerShare_ = poolInfoAccSushiPerShare(otherPid);
	uint64 otherLastRewardBlock_ = poolInfoLastRewardBlock(otherPid);
	uint64 otherAllocPoint_ = poolInfoAllocPoint(otherPid);

	assert(_otherAccSushiPerShare == otherAccSushiPerShare_, "accSushiPerShare changed");

	assert(_otherLastRewardBlock == otherLastRewardBlock_, "lastRewardBlock changed");

	assert(_otherAllocPoint == otherAllocPoint_, "allocPoint changed");
}

rule preserveTotalAssetOfUser(method f, uint256 pid, address user,
					          address to, uint256 amount) {
	require f.selector != init(address).selector;
	env e;

	require user == e.msg.sender && user == to && user != currentContract;
	require SUSHI() != lpToken(pid); // <-- check this again (Nurit)

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

// TODO: (2)
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

rule sushiGivenInHarvestEqualsPendingSushi(uint256 pid, address user, address to) {
	env e;

	require to == user && user != currentContract;
	require sushiToken == SUSHI();

	uint256 userSushiBalance = sushiToken.balanceOf(e, user);
	uint256 userPendingSushi = pendingSushi(e, pid, user);

	// Does success return value matters? Check with Nurit
	harvest(e, pid, to);

	uint256 userSushiBalance_ = sushiToken.balanceOf(e, user);

	assert(userSushiBalance_ == (userSushiBalance + userPendingSushi),
		   "pending sushi not equal to the sushi given in harvest");
}

rule depositThenWithdraw(uint256 pid, address user, uint256 amount, address to) {
	env e;

	require e.msg.sender == to;

	uint256 _userInfoAmount = userInfoAmount(pid, user);
	int256 _userInfoRewardDebt = userInfoRewardDebt(pid, user);

	deposit(e, pid, amount, to);
	withdraw(e, pid, amount, to);

	uint256 userInfoAmount_ = userInfoAmount(pid, user);
	int256 userInfoRewardDebt_ = userInfoRewardDebt(pid, user);

	assert(_userInfoAmount == userInfoAmount_, "user amount changed");
	assert(intEquality(_userInfoRewardDebt, userInfoRewardDebt_),
		   "user reward debt changed");
}

// TODO: (3)
// rule depositThenWithdrawWithRevert() {
	
// }

rule orderOfOperationWithdrawAndHarvest(uint256 pid, uint256 amount, address user) {
	env e;
	storage initStorage = lastStorage;

	// call withdraw then harvest
	withdraw(e, pid, amount, user);
	harvest(e, pid, user);

	uint128 splitScenarioAccSushiPerShare = poolInfoAccSushiPerShare(pid);
	uint64 splitScenarioLastRewardBlock = poolInfoLastRewardBlock(pid);
	uint64 splitScenarioAllocPoint = poolInfoAllocPoint(pid);

	uint256 splitScenarioUserInfoAmount = userInfoAmount(pid, user);
	int256 splitScenarioUserInfoRewardDebt = userInfoRewardDebt(pid, user);

	// call harvest then withdraw at initStorage
	harvest(e, pid, user) at initStorage;
	withdraw(e, pid, amount, user);

	uint128 finalScenarioAccSushiPerShare = poolInfoAccSushiPerShare(pid);
	uint64 finalScenarioLastRewardBlock = poolInfoLastRewardBlock(pid);
	uint64 finalScenarioAllocPoint = poolInfoAllocPoint(pid);

	uint256 finalScenarioUserInfoAmount = userInfoAmount(pid, user);
	int256 finalScenarioUserInfoRewardDebt = userInfoRewardDebt(pid, user);

	assert(splitScenarioAccSushiPerShare == finalScenarioAccSushiPerShare, "finalScenarioAccSushiPerShare");
	assert(splitScenarioLastRewardBlock == finalScenarioLastRewardBlock, "finalScenarioLastRewardBlock");
	assert(splitScenarioAllocPoint == splitScenarioAllocPoint, "splitScenarioAllocPoint");

	assert(splitScenarioUserInfoAmount == finalScenarioUserInfoAmount, "finalScenarioUserInfoAmount");
	assert(intDeltaOne(splitScenarioUserInfoRewardDebt, finalScenarioUserInfoRewardDebt), "finalScenarioUserInfoRewardDebt");
}

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

// Helper Functions

// easy to use dispatcher (to call all methods with the same pid)
function callFunctionWithParams(method f, uint256 pid, uint256 allocPoint,
						        bool overwrite, address user, uint256 amount) {
	env e;

	if (f.selector == set(uint256, uint256, address, bool).selector) {
		set(e, pid, allocPoint, rewarderMock, overwrite);
	} else if (f.selector == pendingSushi(uint256, address).selector) {
		pendingSushi(e, pid, user);
	} else if (f.selector == updatePool(uint256).selector) {
		updatePool(e, pid);
	} else if (f.selector == deposit(uint256, uint256, address).selector) {
		deposit(e, pid, amount, user);
	} else if (f.selector == withdraw(uint256, uint256, address).selector) {
		withdraw(e, pid, amount, user); 
	} else if (f.selector == harvest(uint256, address).selector) {
		harvest(e, pid, user);
	} else if (f.selector == emergencyWithdraw(uint256, address).selector) {
		emergencyWithdraw(e, pid, user);
	} else {
		calldataarg args;
		f(e,args);
	}
}	