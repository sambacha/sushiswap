pragma solidity 0.6.12;
pragma experimental ABIEncoderV2;

import "../../contracts/MasterChefV2.sol";

contract MasterChefV2Harness is MasterChefV2 {
    ////////////////////////////////////////////////////////////////////////////
    //                         Constructors and inits                         //
    ////////////////////////////////////////////////////////////////////////////
    constructor(IMasterChef _MASTER_CHEF, IERC20 _sushi, uint256 _MASTER_PID)
                    MasterChefV2(_MASTER_CHEF, _sushi, _MASTER_PID) public { }

    ////////////////////////////////////////////////////////////////////////////
    //                        Getters for The Internals                       //
    ////////////////////////////////////////////////////////////////////////////
    function userInfoAmount(uint256 pid, address user) public view returns (uint256) {
        return userInfo[pid][user].amount;
    }

    function userInfoRewardDebt(uint256 pid, address user) public view returns (int256) {
        return userInfo[pid][user].rewardDebt;
    }

    function userLpTokenBalanceOf(uint256 pid, address user) public view returns (uint256) {
        return lpToken[pid].balanceOf(user);
    }

    function poolInfoAccSushiPerShare(uint256 pid) public view returns (uint128) {
        return poolInfo[pid].accSushiPerShare;
    }

    function poolInfoLastRewardBlock(uint256 pid) public view returns (uint64) {
        return poolInfo[pid].lastRewardBlock;
    }

    function poolInfoAllocPoint(uint256 pid) public view returns (uint64) {
        return poolInfo[pid].allocPoint;
    }

    ////////////////////////////////////////////////////////////////////////////
    //                           Overrided Methods                            //
    ////////////////////////////////////////////////////////////////////////////
    function batch(bytes[] calldata calls, bool revertOnFail) override external
            payable returns(bool[] memory successes, bytes[] memory results) { }

    mapping(uint256 => uint256) symbolicSushiPerBlock; // random number
    function sushiPerBlock() public view override returns (uint256 amount) {
        return symbolicSushiPerBlock[block.number];
    }

    mapping(uint256 => mapping(uint64 => mapping( uint256 => uint256))) symbolicSushiReward; // random number
    function calculateSushiReward(uint256 blocks, uint64 poolAllocPoint) override internal returns (uint256) {
        return symbolicSushiReward[blocks][poolAllocPoint][totalAllocPoint];
    }

    mapping(uint256 => mapping(uint256 => uint256)) symbolicSushiPerShare; // random number
    function calculateSushiPerShare(uint256 sushiReward, uint256 lpSupply ) override internal returns (uint256) {
        return (sushiReward.mul(ACC_SUSHI_PRECISION) / lpSupply).to128();
    }

    ////////////////////////////////////////////////////////////////////////////
    //                            General Helpers                             //
    ////////////////////////////////////////////////////////////////////////////

    // helpers for int operations since in spec it is not possible
    function compare(int256 x, int256 y) external pure returns (bool) {
		return x <= y;
	}

    function intEquality(int256 x, int256 y) external pure returns (bool) {
        return x == y;
    }

    function compareUint128(uint128 x, uint128 y) external pure returns (bool) {
		return x >= y;
	}

    function intDeltaOne(int256 x, int256 y) external pure returns (bool) {
        int256 difference = x.sub(y);

        return difference >= -1 && difference <= 1;
    }

    ////////////////////////////////////////////////////////////////////////////
    //                     Helper Functions for Invariants                    //
    ////////////////////////////////////////////////////////////////////////////
    // for invariants we need a function that simulate the constructor 
	function init_state() public { }

    function lpTokenLength() public view returns (uint256) {
        return lpToken.length;
    }

    function rewarderLength() public view returns (uint256) {
        return rewarder.length;
    }
}