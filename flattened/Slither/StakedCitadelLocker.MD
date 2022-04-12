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



OwnableUpgradeable.__gap (flattened/StakedCitadelLocker.sol#869) shadows:
	- ContextUpgradeable.__gap (flattened/StakedCitadelLocker.sol#787)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variable-shadowing

StakedCitadelLocker.initialize(address,string,string) (flattened/StakedCitadelLocker.sol#971-990) performs a multiplication on the result of a division:
	-currentEpoch = block.timestamp.div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#983-985)
StakedCitadelLocker.balanceOf(address) (flattened/StakedCitadelLocker.sol#1199-1231) performs a multiplication on the result of a division:
	-currentEpoch = block.timestamp.div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#1219-1221)
StakedCitadelLocker.balanceAtEpochOf(uint256,address) (flattened/StakedCitadelLocker.sol#1234-1268) performs a multiplication on the result of a division:
	-currentEpoch = block.timestamp.div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#1247-1249)
StakedCitadelLocker.totalSupply() (flattened/StakedCitadelLocker.sol#1271-1293) performs a multiplication on the result of a division:
	-currentEpoch = block.timestamp.div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#1272-1274)
StakedCitadelLocker.totalSupplyAtEpoch(uint256) (flattened/StakedCitadelLocker.sol#1296-1324) performs a multiplication on the result of a division:
	-epochStart = uint256(epochs[_epoch].date).div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#1301-1303)
StakedCitadelLocker.totalSupplyAtEpoch(uint256) (flattened/StakedCitadelLocker.sol#1296-1324) performs a multiplication on the result of a division:
	-currentEpoch = block.timestamp.div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#1305-1307)
StakedCitadelLocker.findEpochId(uint256) (flattened/StakedCitadelLocker.sol#1327-1349) performs a multiplication on the result of a division:
	-_time = _time.div(rewardsDuration).mul(rewardsDuration) (flattened/StakedCitadelLocker.sol#1332)
StakedCitadelLocker._checkpointEpoch() (flattened/StakedCitadelLocker.sol#1397-1422) performs a multiplication on the result of a division:
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

Reentrancy in StakedCitadelLocker.lock(address,uint256,uint256) (flattened/StakedCitadelLocker.sol#1425-1435):
	External calls:
	- stakingToken.safeTransferFrom(msg.sender,address(this),_amount) (flattened/StakedCitadelLocker.sol#1431)
	State variables written after the call(s):
	- _lock(_account,_amount,_spendRatio) (flattened/StakedCitadelLocker.sol#1434)
		- bal.locked = bal.locked.add(lockAmount) (flattened/StakedCitadelLocker.sol#1463)
		- bal.boosted = bal.boosted.add(boostedAmount) (flattened/StakedCitadelLocker.sol#1464)
	- _lock(_account,_amount,_spendRatio) (flattened/StakedCitadelLocker.sol#1434)
		- boostedSupply = boostedSupply.add(boostedAmount) (flattened/StakedCitadelLocker.sol#1468)
	- _lock(_account,_amount,_spendRatio) (flattened/StakedCitadelLocker.sol#1434)
		- lockedSupply = lockedSupply.add(lockAmount) (flattened/StakedCitadelLocker.sol#1467)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-1

StakedCitadelLocker.lockedBalances(address).idx (flattened/StakedCitadelLocker.sol#1365) is a local variable never initialized
StakedCitadelLocker.getReward(address,bool).i (flattened/StakedCitadelLocker.sol#1652) is a local variable never initialized
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#uninitialized-local-variables

StakedCitadelLocker.initialize(address,string,string).name (flattened/StakedCitadelLocker.sol#973) shadows:
	- StakedCitadelLocker.name() (flattened/StakedCitadelLocker.sol#996-998) (function)
StakedCitadelLocker.initialize(address,string,string).symbol (flattened/StakedCitadelLocker.sol#974) shadows:
	- StakedCitadelLocker.symbol() (flattened/StakedCitadelLocker.sol#1000-1002) (function)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#local-variable-shadowing

StakedCitadelLocker.setStakeLimits(uint256,uint256) (flattened/StakedCitadelLocker.sol#1042-1051) should emit an event for: 
	- minimumStake = _minimum (flattened/StakedCitadelLocker.sol#1048) 
	- maximumStake = _maximum (flattened/StakedCitadelLocker.sol#1049) 
StakedCitadelLocker.setBoost(uint256,uint256,address) (flattened/StakedCitadelLocker.sol#1054-1065) should emit an event for: 
	- nextMaximumBoostPayment = _max (flattened/StakedCitadelLocker.sol#1062) 
	- nextBoostRate = _rate (flattened/StakedCitadelLocker.sol#1063) 
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#missing-events-arithmetic

StakedCitadelLocker.setStakingContract(address)._staking (flattened/StakedCitadelLocker.sol#1031) lacks a zero-check on :
		- stakingProxy = _staking (flattened/StakedCitadelLocker.sol#1038)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#missing-zero-address-validation

Reentrancy in StakedCitadelLocker.lock(address,uint256,uint256) (flattened/StakedCitadelLocker.sol#1425-1435):
	External calls:
	- stakingToken.safeTransferFrom(msg.sender,address(this),_amount) (flattened/StakedCitadelLocker.sol#1431)
	State variables written after the call(s):
	- _lock(_account,_amount,_spendRatio) (flattened/StakedCitadelLocker.sol#1434)
		- boostRate = nextBoostRate (flattened/StakedCitadelLocker.sol#1416)
	- _lock(_account,_amount,_spendRatio) (flattened/StakedCitadelLocker.sol#1434)
		- epochs.push(Epoch(0,uint32(nextEpochDate))) (flattened/StakedCitadelLocker.sol#1411)
		- e.supply = e.supply.add(uint224(boostedAmount)) (flattened/StakedCitadelLocker.sol#1492)
	- _lock(_account,_amount,_spendRatio) (flattened/StakedCitadelLocker.sol#1434)
		- maximumBoostPayment = nextMaximumBoostPayment (flattened/StakedCitadelLocker.sol#1419)
	- _lock(_account,_amount,_spendRatio) (flattened/StakedCitadelLocker.sol#1434)
		- userLocks[_account].push(LockedBalance(lockAmount,boostedAmount,uint32(unlockTime))) (flattened/StakedCitadelLocker.sol#1477-1483)
		- userL.amount = userL.amount.add(lockAmount) (flattened/StakedCitadelLocker.sol#1486)
		- userL.boosted = userL.boosted.add(boostedAmount) (flattened/StakedCitadelLocker.sol#1487)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-2

Reentrancy in StakedCitadelLocker.getReward(address,bool) (flattened/StakedCitadelLocker.sol#1646-1663):
	External calls:
	- IERC20Upgradeable(_rewardsToken).safeTransfer(_account,reward) (flattened/StakedCitadelLocker.sol#1657)
	Event emitted after the call(s):
	- RewardPaid(_account,_rewardsToken,reward) (flattened/StakedCitadelLocker.sol#1658)
Reentrancy in StakedCitadelLocker.lock(address,uint256,uint256) (flattened/StakedCitadelLocker.sol#1425-1435):
	External calls:
	- stakingToken.safeTransferFrom(msg.sender,address(this),_amount) (flattened/StakedCitadelLocker.sol#1431)
	Event emitted after the call(s):
	- Staked(_account,_amount,lockAmount,boostedAmount) (flattened/StakedCitadelLocker.sol#1494)
		- _lock(_account,_amount,_spendRatio) (flattened/StakedCitadelLocker.sol#1434)
Reentrancy in StakedCitadelLocker.notifyRewardAmount(address,uint256) (flattened/StakedCitadelLocker.sol#1695-1713):
	External calls:
	- IERC20Upgradeable(_rewardsToken).safeTransferFrom(msg.sender,address(this),_reward) (flattened/StakedCitadelLocker.sol#1706-1710)
	Event emitted after the call(s):
	- RewardAdded(_rewardsToken,_reward) (flattened/StakedCitadelLocker.sol#1712)
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

AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/StakedCitadelLocker.sol#485-505) uses assembly
	- INLINE ASM (flattened/StakedCitadelLocker.sol#497-500)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#assembly-usage

AddressUpgradeable.functionCall(address,bytes) (flattened/StakedCitadelLocker.sol#396-398) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256) (flattened/StakedCitadelLocker.sol#425-431) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes) (flattened/StakedCitadelLocker.sol#458-460) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/StakedCitadelLocker.sol#468-477) is never used and should be removed
AddressUpgradeable.sendValue(address,uint256) (flattened/StakedCitadelLocker.sol#371-376) is never used and should be removed
BoringMath.to128(uint256) (flattened/StakedCitadelLocker.sol#65-68) is never used and should be removed
BoringMath.to216(uint256) (flattened/StakedCitadelLocker.sol#100-103) is never used and should be removed
BoringMath.to224(uint256) (flattened/StakedCitadelLocker.sol#90-93) is never used and should be removed
BoringMath.to64(uint256) (flattened/StakedCitadelLocker.sol#70-73) is never used and should be removed
BoringMath112.div(uint112,uint112) (flattened/StakedCitadelLocker.sol#162-165) is never used and should be removed
BoringMath112.mul(uint112,uint112) (flattened/StakedCitadelLocker.sol#158-160) is never used and should be removed
BoringMath128.add(uint128,uint128) (flattened/StakedCitadelLocker.sol#108-110) is never used and should be removed
BoringMath128.sub(uint128,uint128) (flattened/StakedCitadelLocker.sol#112-114) is never used and should be removed
BoringMath224.div(uint224,uint224) (flattened/StakedCitadelLocker.sol#182-185) is never used and should be removed
BoringMath224.mul(uint224,uint224) (flattened/StakedCitadelLocker.sol#178-180) is never used and should be removed
BoringMath224.sub(uint224,uint224) (flattened/StakedCitadelLocker.sol#174-176) is never used and should be removed
BoringMath32.add(uint32,uint32) (flattened/StakedCitadelLocker.sol#130-132) is never used and should be removed
BoringMath32.div(uint32,uint32) (flattened/StakedCitadelLocker.sol#142-145) is never used and should be removed
BoringMath32.mul(uint32,uint32) (flattened/StakedCitadelLocker.sol#138-140) is never used and should be removed
BoringMath32.sub(uint32,uint32) (flattened/StakedCitadelLocker.sol#134-136) is never used and should be removed
BoringMath64.add(uint64,uint64) (flattened/StakedCitadelLocker.sol#119-121) is never used and should be removed
BoringMath64.sub(uint64,uint64) (flattened/StakedCitadelLocker.sol#123-125) is never used and should be removed
ContextUpgradeable.__Context_init() (flattened/StakedCitadelLocker.sol#769-770) is never used and should be removed
ContextUpgradeable.__Context_init_unchained() (flattened/StakedCitadelLocker.sol#772-773) is never used and should be removed
ContextUpgradeable._msgData() (flattened/StakedCitadelLocker.sol#778-780) is never used and should be removed
MathUpgradeable.average(uint256,uint256) (flattened/StakedCitadelLocker.sol#293-296) is never used and should be removed
MathUpgradeable.ceilDiv(uint256,uint256) (flattened/StakedCitadelLocker.sol#304-307) is never used and should be removed
MathUpgradeable.max(uint256,uint256) (flattened/StakedCitadelLocker.sol#278-280) is never used and should be removed
MathUtil.min(uint256,uint256) (flattened/StakedCitadelLocker.sol#12-14) is never used and should be removed
SafeERC20Upgradeable.safeApprove(IERC20Upgradeable,address,uint256) (flattened/StakedCitadelLocker.sol#544-557) is never used and should be removed
SafeERC20Upgradeable.safeDecreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/StakedCitadelLocker.sol#568-579) is never used and should be removed
SafeERC20Upgradeable.safeIncreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/StakedCitadelLocker.sol#559-566) is never used and should be removed
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dead-code

Pragma version0.8.12 (flattened/StakedCitadelLocker.sol#2) necessitates a version too recent to be trusted. Consider deploying with 0.6.12/0.7.6/0.8.7
solc-0.8.12 is not recommended for deployment
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#incorrect-versions-of-solidity

Low level call in AddressUpgradeable.sendValue(address,uint256) (flattened/StakedCitadelLocker.sol#371-376):
	- (success) = recipient.call{value: amount}() (flattened/StakedCitadelLocker.sol#374)
Low level call in AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/StakedCitadelLocker.sol#439-450):
	- (success,returndata) = target.call{value: value}(data) (flattened/StakedCitadelLocker.sol#448)
Low level call in AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/StakedCitadelLocker.sol#468-477):
	- (success,returndata) = target.staticcall(data) (flattened/StakedCitadelLocker.sol#475)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#low-level-calls

Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init() (flattened/StakedCitadelLocker.sol#714-716) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init_unchained() (flattened/StakedCitadelLocker.sol#718-720) is not in mixedCase
Variable ReentrancyGuardUpgradeable.__gap (flattened/StakedCitadelLocker.sol#748) is not in mixedCase
Function ContextUpgradeable.__Context_init() (flattened/StakedCitadelLocker.sol#769-770) is not in mixedCase
Function ContextUpgradeable.__Context_init_unchained() (flattened/StakedCitadelLocker.sol#772-773) is not in mixedCase
Variable ContextUpgradeable.__gap (flattened/StakedCitadelLocker.sol#787) is not in mixedCase
Function OwnableUpgradeable.__Ownable_init() (flattened/StakedCitadelLocker.sol#811-813) is not in mixedCase
Function OwnableUpgradeable.__Ownable_init_unchained() (flattened/StakedCitadelLocker.sol#815-817) is not in mixedCase
Variable OwnableUpgradeable.__gap (flattened/StakedCitadelLocker.sol#869) is not in mixedCase
Parameter StakedCitadelLocker.initialize(address,string,string)._stakingToken (flattened/StakedCitadelLocker.sol#972) is not in mixedCase
Parameter StakedCitadelLocker.addReward(address,address)._rewardsToken (flattened/StakedCitadelLocker.sol#1008) is not in mixedCase
Parameter StakedCitadelLocker.addReward(address,address)._distributor (flattened/StakedCitadelLocker.sol#1008) is not in mixedCase
Parameter StakedCitadelLocker.approveRewardDistributor(address,address,bool)._rewardsToken (flattened/StakedCitadelLocker.sol#1022) is not in mixedCase
Parameter StakedCitadelLocker.approveRewardDistributor(address,address,bool)._distributor (flattened/StakedCitadelLocker.sol#1023) is not in mixedCase
Parameter StakedCitadelLocker.approveRewardDistributor(address,address,bool)._approved (flattened/StakedCitadelLocker.sol#1024) is not in mixedCase
Parameter StakedCitadelLocker.setStakingContract(address)._staking (flattened/StakedCitadelLocker.sol#1031) is not in mixedCase
Parameter StakedCitadelLocker.setStakeLimits(uint256,uint256)._minimum (flattened/StakedCitadelLocker.sol#1042) is not in mixedCase
Parameter StakedCitadelLocker.setStakeLimits(uint256,uint256)._maximum (flattened/StakedCitadelLocker.sol#1042) is not in mixedCase
Parameter StakedCitadelLocker.setBoost(uint256,uint256,address)._max (flattened/StakedCitadelLocker.sol#1055) is not in mixedCase
Parameter StakedCitadelLocker.setBoost(uint256,uint256,address)._rate (flattened/StakedCitadelLocker.sol#1056) is not in mixedCase
Parameter StakedCitadelLocker.setBoost(uint256,uint256,address)._receivingAddress (flattened/StakedCitadelLocker.sol#1057) is not in mixedCase
Parameter StakedCitadelLocker.setKickIncentive(uint256,uint256)._rate (flattened/StakedCitadelLocker.sol#1068) is not in mixedCase
Parameter StakedCitadelLocker.setKickIncentive(uint256,uint256)._delay (flattened/StakedCitadelLocker.sol#1068) is not in mixedCase
Parameter StakedCitadelLocker.lastTimeRewardApplicable(address)._rewardsToken (flattened/StakedCitadelLocker.sol#1133) is not in mixedCase
Parameter StakedCitadelLocker.rewardPerToken(address)._rewardsToken (flattened/StakedCitadelLocker.sol#1142) is not in mixedCase
Parameter StakedCitadelLocker.getRewardForDuration(address)._rewardsToken (flattened/StakedCitadelLocker.sol#1150) is not in mixedCase
Parameter StakedCitadelLocker.claimableRewards(address)._account (flattened/StakedCitadelLocker.sol#1160) is not in mixedCase
Parameter StakedCitadelLocker.rewardWeightOf(address)._user (flattened/StakedCitadelLocker.sol#1181) is not in mixedCase
Parameter StakedCitadelLocker.lockedBalanceOf(address)._user (flattened/StakedCitadelLocker.sol#1190) is not in mixedCase
Parameter StakedCitadelLocker.balanceOf(address)._user (flattened/StakedCitadelLocker.sol#1199) is not in mixedCase
Parameter StakedCitadelLocker.balanceAtEpochOf(uint256,address)._epoch (flattened/StakedCitadelLocker.sol#1234) is not in mixedCase
Parameter StakedCitadelLocker.balanceAtEpochOf(uint256,address)._user (flattened/StakedCitadelLocker.sol#1234) is not in mixedCase
Parameter StakedCitadelLocker.totalSupplyAtEpoch(uint256)._epoch (flattened/StakedCitadelLocker.sol#1296) is not in mixedCase
Parameter StakedCitadelLocker.findEpochId(uint256)._time (flattened/StakedCitadelLocker.sol#1327) is not in mixedCase
Parameter StakedCitadelLocker.lockedBalances(address)._user (flattened/StakedCitadelLocker.sol#1352) is not in mixedCase
Parameter StakedCitadelLocker.lock(address,uint256,uint256)._account (flattened/StakedCitadelLocker.sol#1426) is not in mixedCase
Parameter StakedCitadelLocker.lock(address,uint256,uint256)._amount (flattened/StakedCitadelLocker.sol#1427) is not in mixedCase
Parameter StakedCitadelLocker.lock(address,uint256,uint256)._spendRatio (flattened/StakedCitadelLocker.sol#1428) is not in mixedCase
Parameter StakedCitadelLocker.processExpiredLocks(bool,uint256,address)._relock (flattened/StakedCitadelLocker.sol#1564) is not in mixedCase
Parameter StakedCitadelLocker.processExpiredLocks(bool,uint256,address)._spendRatio (flattened/StakedCitadelLocker.sol#1565) is not in mixedCase
Parameter StakedCitadelLocker.processExpiredLocks(bool,uint256,address)._withdrawTo (flattened/StakedCitadelLocker.sol#1566) is not in mixedCase
Parameter StakedCitadelLocker.processExpiredLocks(bool)._relock (flattened/StakedCitadelLocker.sol#1579) is not in mixedCase
Parameter StakedCitadelLocker.kickExpiredLocks(address)._account (flattened/StakedCitadelLocker.sol#1584) is not in mixedCase
Parameter StakedCitadelLocker.transferCVX(address,uint256,bool)._account (flattened/StakedCitadelLocker.sol#1603) is not in mixedCase
Parameter StakedCitadelLocker.transferCVX(address,uint256,bool)._amount (flattened/StakedCitadelLocker.sol#1604) is not in mixedCase
Parameter StakedCitadelLocker.updateStakeRatio(uint256)._offset (flattened/StakedCitadelLocker.sol#1614) is not in mixedCase
Parameter StakedCitadelLocker.getReward(address,bool)._account (flattened/StakedCitadelLocker.sol#1646) is not in mixedCase
Parameter StakedCitadelLocker.getReward(address)._account (flattened/StakedCitadelLocker.sol#1666) is not in mixedCase
Parameter StakedCitadelLocker.notifyRewardAmount(address,uint256)._rewardsToken (flattened/StakedCitadelLocker.sol#1695) is not in mixedCase
Parameter StakedCitadelLocker.notifyRewardAmount(address,uint256)._reward (flattened/StakedCitadelLocker.sol#1695) is not in mixedCase
Parameter StakedCitadelLocker.recoverERC20(address,uint256)._tokenAddress (flattened/StakedCitadelLocker.sol#1716) is not in mixedCase
Parameter StakedCitadelLocker.recoverERC20(address,uint256)._tokenAmount (flattened/StakedCitadelLocker.sol#1716) is not in mixedCase
Constant StakedCitadelLocker.rewardsDuration (flattened/StakedCitadelLocker.sol#919) is not in UPPER_CASE_WITH_UNDERSCORES
Constant StakedCitadelLocker.lockDuration (flattened/StakedCitadelLocker.sol#922) is not in UPPER_CASE_WITH_UNDERSCORES
Constant StakedCitadelLocker.denominator (flattened/StakedCitadelLocker.sol#948) is not in UPPER_CASE_WITH_UNDERSCORES
Constant StakedCitadelLocker.stakeOffsetOnLock (flattened/StakedCitadelLocker.sol#954) is not in UPPER_CASE_WITH_UNDERSCORES
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#conformance-to-solidity-naming-conventions

OwnableUpgradeable.__gap (flattened/StakedCitadelLocker.sol#869) is never used in StakedCitadelLocker (flattened/StakedCitadelLocker.sol#872-1784)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-state-variable

renounceOwnership() should be declared external:
	- OwnableUpgradeable.renounceOwnership() (flattened/StakedCitadelLocker.sol#841-843)
transferOwnership(address) should be declared external:
	- OwnableUpgradeable.transferOwnership(address) (flattened/StakedCitadelLocker.sol#849-852)
initialize(address,string,string) should be declared external:
	- StakedCitadelLocker.initialize(address,string,string) (flattened/StakedCitadelLocker.sol#971-990)
decimals() should be declared external:
	- StakedCitadelLocker.decimals() (flattened/StakedCitadelLocker.sol#992-994)
name() should be declared external:
	- StakedCitadelLocker.name() (flattened/StakedCitadelLocker.sol#996-998)
symbol() should be declared external:
	- StakedCitadelLocker.symbol() (flattened/StakedCitadelLocker.sol#1000-1002)
addReward(address,address) should be declared external:
	- StakedCitadelLocker.addReward(address,address) (flattened/StakedCitadelLocker.sol#1008-1018)
lastTimeRewardApplicable(address) should be declared external:
	- StakedCitadelLocker.lastTimeRewardApplicable(address) (flattened/StakedCitadelLocker.sol#1133-1140)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#public-function-that-could-be-declared-external
flattened/StakedCitadelLocker.sol analyzed (18 contracts with 77 detectors), 147 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
