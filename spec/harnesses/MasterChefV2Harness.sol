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
    function userInfoAmount(uint256 pid, address user) public view returns (uint256 amount) {
        return userInfo[pid][user].amount;
    }

    function userInfoRewardDebt(uint256 pid, address user) public view returns (int256 rewardDebt) {
        return userInfo[pid][user].rewardDebt;
    }

    ////////////////////////////////////////////////////////////////////////////
    //                           Overrided Methods                            //
    ////////////////////////////////////////////////////////////////////////////

    // If needed ...
     function batch(bytes[] calldata calls, bool revertOnFail) override external payable returns(bool[] memory successes, bytes[] memory results) {
     }   
}