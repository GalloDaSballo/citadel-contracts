  

Funding.getAmountOut(uint256) (flattened/Funding.sol#1415-1430) performs a multiplication on the result of a division:
	-citadelAmountWithoutDiscount = (_assetAmountIn * citadelPriceInAsset) / assetDecimalsNormalizationValue (flattened/Funding.sol#1420-1421)
	-citadelAmount_ = (citadelAmountWithoutDiscount * MAX_BPS) / (MAX_BPS - funding.discount) (flattened/Funding.sol#1424-1426)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#divide-before-multiply

Funding.initialize(address,address,address,address,address,address,uint256) (flattened/Funding.sol#1318-1352) ignores return value by citadel.approve(address(xCitadel),type()(uint256).max) (flattened/Funding.sol#1345)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-return


Funding.initialize(address,address,address,address,address,address,uint256)._citadelPriceInAssetOracle (flattened/Funding.sol#1324) lacks a zero-check on :
		- citadelPriceInAssetOracle = _citadelPriceInAssetOracle (flattened/Funding.sol#1340)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#missing-zero-address-validation



Reentrancy in Funding.initialize(address,address,address,address,address,address,uint256) (flattened/Funding.sol#1318-1352):
	External calls:
	- citadel.approve(address(xCitadel),type()(uint256).max) (flattened/Funding.sol#1345)
	State variables written after the call(s):
	- assetDecimalsNormalizationValue = 10 ** asset.decimals() (flattened/Funding.sol#1347)
	- maxCitadelPriceInAsset = type()(uint256).max (flattened/Funding.sol#1351)
	- minCitadelPriceInAsset = 0 (flattened/Funding.sol#1350)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-2


Acknowledged, who cares
Reentrancy in Funding.claimAssetToTreasury() (flattened/Funding.sol#1525-1535):
	External calls:
	- asset.safeTransfer(saleRecipient,amount) (flattened/Funding.sol#1532)
	Event emitted after the call(s):
	- ClaimToTreasury(address(asset),amount) (flattened/Funding.sol#1534)


Acknowledged, who cares
Reentrancy in Funding.deposit(uint256,uint256) (flattened/Funding.sol#1372-1404):
	External calls:
	- asset.safeTransferFrom(msg.sender,saleRecipient,_assetAmountIn) (flattened/Funding.sol#1389)
	- xCitadel.depositFor(msg.sender,citadelAmount_) (flattened/Funding.sol#1394)
	Event emitted after the call(s):
	- Deposit(msg.sender,_assetAmountIn,xCitadelGained,citadelAmount_) (flattened/Funding.sol#1398-1403)


Acknowledged, who cares
Reentrancy in Funding.sweep(address) (flattened/Funding.sol#1507-1521):
	External calls:
	- IERC20(_token).safeTransfer(saleRecipient,amount) (flattened/Funding.sol#1519)
	Event emitted after the call(s):
	- Sweep(_token,amount) (flattened/Funding.sol#1520)




-> UNUSED STORAGE VAR = 20k gas wasted
Funding.xCitadelPriceInAsset (flattened/Funding.sol#1252) should be constant
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variables-that-could-be-declared-constant
flattened/Funding.sol analyzed (14 contracts with 77 detectors), 81 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
