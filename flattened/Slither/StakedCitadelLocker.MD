entreprenerd@MacBook-Pro citadel-contracts % slither flattened/StakedCitadelLocker.sol
Compilation warnings/errors on flattened/StakedCitadelLocker.sol:
Warning: This declaration shadows an existing declaration.
   --> flattened/StakedCitadelLocker.sol:973:9:
    |
973 |         string memory name,
    |         ^^^^^^^^^^^^^^^^^^
Note: The shadowed declaration is here:
   --> flattened/StakedCitadelLocker.sol:996:5:
    |
996 |     function name() public view returns (string memory) {
    |     ^ (Relevant source part starts here and spans across multiple lines).

Warning: This declaration shadows an existing declaration.
   --> flattened/StakedCitadelLocker.sol:974:9:
    |
974 |         string memory symbol
    |         ^^^^^^^^^^^^^^^^^^^^
Note: The shadowed declaration is here:
    --> flattened/StakedCitadelLocker.sol:1000:5:
     |
1000 |     function symbol() public view returns (string memory) {
     |     ^ (Relevant source part starts here and spans across multiple lines).

Warning: Unused function parameter. Remove or comment out the variable name to silence this warning.
    --> flattened/StakedCitadelLocker.sol:1502:9:
     |
1502 |         uint256 _spendRatio,
     |         ^^^^^^^^^^^^^^^^^^^

Warning: Unused function parameter. Remove or comment out the variable name to silence this warning.
    --> flattened/StakedCitadelLocker.sol:1504:9:
     |
1504 |         address _rewardAddress,
     |         ^^^^^^^^^^^^^^^^^^^^^^

Warning: Unused local variable.
    --> flattened/StakedCitadelLocker.sol:1512:9:
     |
1512 |         uint256 reward = 0;
     |         ^^^^^^^^^^^^^^

Warning: Unused function parameter. Remove or comment out the variable name to silence this warning.
    --> flattened/StakedCitadelLocker.sol:1597:37:
     |
1597 |     function allocateCVXForTransfer(uint256 _amount) internal {
     |                                     ^^^^^^^^^^^^^^^

Warning: Unused local variable.
    --> flattened/StakedCitadelLocker.sol:1598:9:
     |
1598 |         uint256 balance = stakingToken.balanceOf(address(this));
     |         ^^^^^^^^^^^^^^^

Warning: Unused function parameter. Remove or comment out the variable name to silence this warning.
    --> flattened/StakedCitadelLocker.sol:1605:9:
     |
1605 |         bool _updateStake
     |         ^^^^^^^^^^^^^^^^^

Warning: Unused function parameter. Remove or comment out the variable name to silence this warning.
    --> flattened/StakedCitadelLocker.sol:1646:42:
     |
1646 |     function getReward(address _account, bool _stake)
     |                                          ^^^^^^^^^^^

Warning: Function state mutability can be restricted to view
    --> flattened/StakedCitadelLocker.sol:1597:5:
     |
1597 |     function allocateCVXForTransfer(uint256 _amount) internal {
     |     ^ (Relevant source part starts here and spans across multiple lines).

Warning: Contract code size is 37273 bytes and exceeds 24576 bytes (a limit introduced in Spurious Dragon). This contract may not be deployable on mainnet. Consider enabling the optimizer (with a low "runs" value!), turning off revert strings, or using libraries.
   --> flattened/StakedCitadelLocker.sol:872:1:
    |
872 | contract StakedCitadelLocker is
    | ^ (Relevant source part starts here and spans across multiple lines).


```
        uint256 currentEpoch = block.timestamp.div(rewardsDuration).mul(
            rewardsDuration
        );

				uint256(epochs[_epoch].date).div(rewardsDuration).mul(rewardsDuration)

				_time.div(rewardsDuration).mul(rewardsDuration)

				_amount.add(_amount.mul(boostRatio).div(denominator)).to112()
				
```
div and then mul





	-currentEpoch = block.timestamp.div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#1398-1400)
StakedCitadelLocker._lock(address,uint256,uint256) (flattened/StakedCitadelLocker.sol#1438-1495) performs a multiplication on the result of a division:
	-boostedAmount = _amount.add(_amount.mul(boostRatio).div(denominator)).to112() (flattened/StakedCitadelLocker.sol#1458-1460)
	-boostRatio = boostRate.mul(_spendRatio).div(maximumBoostPayment) (flattened/StakedCitadelLocker.sol#1454-1456)
StakedCitadelLocker._lock(address,uint256,uint256) (flattened/StakedCitadelLocker.sol#1438-1495) performs a multiplication on the result of a division:
	-currentEpoch = block.timestamp.div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#1471-1473)
StakedCitadelLocker.updateStakeRatio(uint256) (flattened/StakedCitadelLocker.sol#1614-1643) performs a multiplication on the result of a division:
	-mean = maximumStake.add(minimumStake).div(2) (flattened/StakedCitadelLocker.sol#1630)
	-remove = staked.sub(total.mul(mean).div(denominator)) (flattened/StakedCitadelLocker.sol#1635)
StakedCitadelLocker.updateStakeRatio(uint256) (flattened/StakedCitadelLocker.sol#1614-1643) performs a multiplication on the result of a division:
	-mean = maximumStake.add(minimumStake).div(2) (flattened/StakedCitadelLocker.sol#1630)
	-increase = total.mul(mean).div(denominator).sub(staked) (flattened/StakedCitadelLocker.sol#1639)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#divide-before-multiply




StakedCitadelLocker.balanceOf(address) (flattened/StakedCitadelLocker.sol#1199-1231) uses a dangerous strict equality:
	- locksLength > 0 && uint256(locks[locksLength - 1].unlockTime).sub(lockDuration) == currentEpoch (flattened/StakedCitadelLocker.sol#1223-1225)
StakedCitadelLocker.findEpochId(uint256) (flattened/StakedCitadelLocker.sol#1327-1349) uses a dangerous strict equality:
	- midEpochBlock == _time (flattened/StakedCitadelLocker.sol#1339)
StakedCitadelLocker.totalSupply() (flattened/StakedCitadelLocker.sol#1271-1293) uses a dangerous strict equality:
	- uint256(epochs[epochindex - 1].date) == currentEpoch (flattened/StakedCitadelLocker.sol#1279)
StakedCitadelLocker.totalSupplyAtEpoch(uint256) (flattened/StakedCitadelLocker.sol#1296-1324) uses a dangerous strict equality:
	- uint256(epochs[_epoch].date) == currentEpoch (flattened/StakedCitadelLocker.sol#1310)
StakedCitadelLocker.updateStakeRatio(uint256) (flattened/StakedCitadelLocker.sol#1614-1643) uses a dangerous strict equality:
	- total == 0 (flattened/StakedCitadelLocker.sol#1625)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dangerous-strict-equalities





StakedCitadelLocker.setStakingContract(address)._staking (flattened/StakedCitadelLocker.sol#1031) lacks a zero-check on :
		- stakingProxy = _staking (flattened/StakedCitadelLocker.sol#1038)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#missing-zero-address-validation




Just the event
Reentrancy in StakedCitadelLocker.notifyRewardAmount(address,uint256) (flattened/StakedCitadelLocker.sol#1695-1713):
	External calls:
	- IERC20Upgradeable(_rewardsToken).safeTransferFrom(msg.sender,address(this),_reward) (flattened/StakedCitadelLocker.sol#1706-1710)
	Event emitted after the call(s):
	- RewardAdded(_rewardsToken,_reward) (flattened/StakedCitadelLocker.sol#1712)

Just the event
Reentrancy in StakedCitadelLocker.recoverERC20(address,uint256) (flattened/StakedCitadelLocker.sol#1716-1730):
	External calls:
	- IERC20Upgradeable(_tokenAddress).safeTransfer(owner(),_tokenAmount) (flattened/StakedCitadelLocker.sol#1728)
	Event emitted after the call(s):
	- Recovered(_tokenAddress,_tokenAmount) (flattened/StakedCitadelLocker.sol#1729)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-3


StakedCitadelLocker.addReward(address,address) (flattened/StakedCitadelLocker.sol#1008-1018) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool)(rewardData[_rewardsToken].lastUpdateTime == 0) (flattened/StakedCitadelLocker.sol#1012)
StakedCitadelLocker.approveRewardDistributor(address,address,bool) (flattened/StakedCitadelLocker.sol#1021-1028) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool)(rewardData[_rewardsToken].lastUpdateTime > 0) (flattened/StakedCitadelLocker.sol#1026)
StakedCitadelLocker.balanceOf(address) (flattened/StakedCitadelLocker.sol#1199-1231) uses timestamp for comparisons
	Dangerous comparisons:
	- locks[i].unlockTime <= block.timestamp (flattened/StakedCitadelLocker.sol#1210)
	- locksLength > 0 && uint256(locks[locksLength - 1].unlockTime).sub(lockDuration) == currentEpoch (flattened/StakedCitadelLocker.sol#1223-1225)
StakedCitadelLocker.balanceAtEpochOf(uint256,address) (flattened/StakedCitadelLocker.sol#1234-1268) uses timestamp for comparisons
	Dangerous comparisons:
	- lockEpoch <= epochTime && lockEpoch < currentEpoch (flattened/StakedCitadelLocker.sol#1257)
	- lockEpoch > cutoffEpoch (flattened/StakedCitadelLocker.sol#1258)
StakedCitadelLocker.totalSupply() (flattened/StakedCitadelLocker.sol#1271-1293) uses timestamp for comparisons
	Dangerous comparisons:
	- uint256(epochs[epochindex - 1].date) == currentEpoch (flattened/StakedCitadelLocker.sol#1279)
	- i + 1 != 0 (flattened/StakedCitadelLocker.sol#1284)
	- uint256(e.date) <= cutoffEpoch (flattened/StakedCitadelLocker.sol#1286)
StakedCitadelLocker.totalSupplyAtEpoch(uint256) (flattened/StakedCitadelLocker.sol#1296-1324) uses timestamp for comparisons
	Dangerous comparisons:
	- uint256(epochs[_epoch].date) == currentEpoch (flattened/StakedCitadelLocker.sol#1310)
	- uint256(e.date) <= cutoffEpoch (flattened/StakedCitadelLocker.sol#1317)
StakedCitadelLocker.findEpochId(uint256) (flattened/StakedCitadelLocker.sol#1327-1349) uses timestamp for comparisons
	Dangerous comparisons:
	- min >= max (flattened/StakedCitadelLocker.sol#1335)
	- midEpochBlock == _time (flattened/StakedCitadelLocker.sol#1339)
	- midEpochBlock < _time (flattened/StakedCitadelLocker.sol#1342)
StakedCitadelLocker.lockedBalances(address) (flattened/StakedCitadelLocker.sol#1352-1383) uses timestamp for comparisons
	Dangerous comparisons:
	- locks[i].unlockTime > block.timestamp (flattened/StakedCitadelLocker.sol#1369)
StakedCitadelLocker._checkpointEpoch() (flattened/StakedCitadelLocker.sol#1397-1422) uses timestamp for comparisons
	Dangerous comparisons:
	- epochs[epochindex - 1].date < currentEpoch (flattened/StakedCitadelLocker.sol#1406)
	- epochs[epochs.length - 1].date != currentEpoch (flattened/StakedCitadelLocker.sol#1408)
StakedCitadelLocker._lock(address,uint256,uint256) (flattened/StakedCitadelLocker.sol#1438-1495) uses timestamp for comparisons
	Dangerous comparisons:
	- idx == 0 || userLocks[_account][idx - 1].unlockTime < unlockTime (flattened/StakedCitadelLocker.sol#1476)
StakedCitadelLocker._processExpiredLocks(address,bool,uint256,address,address,uint256) (flattened/StakedCitadelLocker.sol#1499-1560) uses timestamp for comparisons
	Dangerous comparisons:
	- isShutdown || locks[length - 1].unlockTime <= block.timestamp.sub(_checkDelay) (flattened/StakedCitadelLocker.sol#1516-1517)
	- locks[i].unlockTime > block.timestamp.sub(_checkDelay) (flattened/StakedCitadelLocker.sol#1531)
StakedCitadelLocker._notifyReward(address,uint256) (flattened/StakedCitadelLocker.sol#1672-1693) uses timestamp for comparisons
	Dangerous comparisons:
	- block.timestamp >= cachedrDataPeriodFinish (flattened/StakedCitadelLocker.sol#1678)
StakedCitadelLocker.recoverERC20(address,uint256) (flattened/StakedCitadelLocker.sol#1716-1730) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(rewardData[_tokenAddress].lastUpdateTime == 0,Cannot withdraw reward token) (flattened/StakedCitadelLocker.sol#1724-1727)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#block-timestamp