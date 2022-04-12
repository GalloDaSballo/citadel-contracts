entreprenerd@MacBook-Pro citadel-contracts % slither flattened/Funding.sol      

PausableUpgradeable.__gap (flattened/Funding.sol#1013) shadows:
	- ContextUpgradeable.__gap (flattened/Funding.sol#916)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variable-shadowing

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

Reentrancy in Funding.claimAssetToTreasury() (flattened/Funding.sol#1525-1535):
	External calls:
	- asset.safeTransfer(saleRecipient,amount) (flattened/Funding.sol#1532)
	Event emitted after the call(s):
	- ClaimToTreasury(address(asset),amount) (flattened/Funding.sol#1534)
Reentrancy in Funding.deposit(uint256,uint256) (flattened/Funding.sol#1372-1404):
	External calls:
	- asset.safeTransferFrom(msg.sender,saleRecipient,_assetAmountIn) (flattened/Funding.sol#1389)
	- xCitadel.depositFor(msg.sender,citadelAmount_) (flattened/Funding.sol#1394)
	Event emitted after the call(s):
	- Deposit(msg.sender,_assetAmountIn,xCitadelGained,citadelAmount_) (flattened/Funding.sol#1398-1403)
Reentrancy in Funding.sweep(address) (flattened/Funding.sol#1507-1521):
	External calls:
	- IERC20(_token).safeTransfer(saleRecipient,amount) (flattened/Funding.sol#1519)
	Event emitted after the call(s):
	- Sweep(_token,amount) (flattened/Funding.sol#1520)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-3

AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/Funding.sol#486-506) uses assembly
	- INLINE ASM (flattened/Funding.sol#498-501)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#assembly-usage

GlobalAccessControlManaged.gacPausable() (flattened/Funding.sol#1103-1107) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/Funding.sol#1105)
GlobalAccessControlManaged.gacPausable() (flattened/Funding.sol#1103-1107) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/Funding.sol#1104)
Funding.onlyWhenPriceNotFlagged() (flattened/Funding.sol#1354-1360) compares to a boolean constant:
	-require(bool,string)(citadelPriceFlag == false,Funding: citadel price from oracle flagged and pending review) (flattened/Funding.sol#1355-1358)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality

AddressUpgradeable.functionCall(address,bytes) (flattened/Funding.sol#397-399) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256) (flattened/Funding.sol#426-432) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes) (flattened/Funding.sol#459-461) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/Funding.sol#469-478) is never used and should be removed
AddressUpgradeable.sendValue(address,uint256) (flattened/Funding.sol#372-377) is never used and should be removed
ContextUpgradeable.__Context_init() (flattened/Funding.sol#898-899) is never used and should be removed
ContextUpgradeable.__Context_init_unchained() (flattened/Funding.sol#901-902) is never used and should be removed
ContextUpgradeable._msgData() (flattened/Funding.sol#907-909) is never used and should be removed
PausableUpgradeable.__Pausable_init() (flattened/Funding.sol#945-947) is never used and should be removed
SafeERC20.safeApprove(IERC20,address,uint256) (flattened/Funding.sol#1167-1180) is never used and should be removed
SafeERC20.safeDecreaseAllowance(IERC20,address,uint256) (flattened/Funding.sol#1191-1202) is never used and should be removed
SafeERC20.safeIncreaseAllowance(IERC20,address,uint256) (flattened/Funding.sol#1182-1189) is never used and should be removed
SafeERC20Upgradeable._callOptionalReturn(IERC20Upgradeable,bytes) (flattened/Funding.sol#588-598) is never used and should be removed
SafeERC20Upgradeable.safeApprove(IERC20Upgradeable,address,uint256) (flattened/Funding.sol#545-558) is never used and should be removed
SafeERC20Upgradeable.safeDecreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/Funding.sol#569-580) is never used and should be removed
SafeERC20Upgradeable.safeIncreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/Funding.sol#560-567) is never used and should be removed
SafeERC20Upgradeable.safeTransfer(IERC20Upgradeable,address,uint256) (flattened/Funding.sol#521-527) is never used and should be removed
SafeERC20Upgradeable.safeTransferFrom(IERC20Upgradeable,address,address,uint256) (flattened/Funding.sol#529-536) is never used and should be removed
SafeMathUpgradeable.div(uint256,uint256) (flattened/Funding.sol#137-139) is never used and should be removed
SafeMathUpgradeable.div(uint256,uint256,string) (flattened/Funding.sol#193-202) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256) (flattened/Funding.sol#153-155) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256,string) (flattened/Funding.sol#219-228) is never used and should be removed
SafeMathUpgradeable.mul(uint256,uint256) (flattened/Funding.sol#123-125) is never used and should be removed
SafeMathUpgradeable.sub(uint256,uint256,string) (flattened/Funding.sol#170-179) is never used and should be removed
SafeMathUpgradeable.tryAdd(uint256,uint256) (flattened/Funding.sol#24-30) is never used and should be removed
SafeMathUpgradeable.tryDiv(uint256,uint256) (flattened/Funding.sol#66-71) is never used and should be removed
SafeMathUpgradeable.tryMod(uint256,uint256) (flattened/Funding.sol#78-83) is never used and should be removed
SafeMathUpgradeable.tryMul(uint256,uint256) (flattened/Funding.sol#49-59) is never used and should be removed
SafeMathUpgradeable.trySub(uint256,uint256) (flattened/Funding.sol#37-42) is never used and should be removed
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dead-code

Pragma version0.8.12 (flattened/Funding.sol#2) necessitates a version too recent to be trusted. Consider deploying with 0.6.12/0.7.6/0.8.7
solc-0.8.12 is not recommended for deployment
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#incorrect-versions-of-solidity

Low level call in AddressUpgradeable.sendValue(address,uint256) (flattened/Funding.sol#372-377):
	- (success) = recipient.call{value: amount}() (flattened/Funding.sol#375)
Low level call in AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/Funding.sol#440-451):
	- (success,returndata) = target.call{value: value}(data) (flattened/Funding.sol#449)
Low level call in AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/Funding.sol#469-478):
	- (success,returndata) = target.staticcall(data) (flattened/Funding.sol#476)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#low-level-calls

Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init() (flattened/Funding.sol#715-717) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init_unchained() (flattened/Funding.sol#719-721) is not in mixedCase
Variable ReentrancyGuardUpgradeable.__gap (flattened/Funding.sol#749) is not in mixedCase
Function ContextUpgradeable.__Context_init() (flattened/Funding.sol#898-899) is not in mixedCase
Function ContextUpgradeable.__Context_init_unchained() (flattened/Funding.sol#901-902) is not in mixedCase
Variable ContextUpgradeable.__gap (flattened/Funding.sol#916) is not in mixedCase
Function PausableUpgradeable.__Pausable_init() (flattened/Funding.sol#945-947) is not in mixedCase
Function PausableUpgradeable.__Pausable_init_unchained() (flattened/Funding.sol#949-951) is not in mixedCase
Variable PausableUpgradeable.__gap (flattened/Funding.sol#1013) is not in mixedCase
Function GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address) (flattened/Funding.sol#1060-1066) is not in mixedCase
Parameter GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address)._globalAccessControl (flattened/Funding.sol#1060) is not in mixedCase
Parameter Funding.initialize(address,address,address,address,address,address,uint256)._gac (flattened/Funding.sol#1319) is not in mixedCase
Parameter Funding.initialize(address,address,address,address,address,address,uint256)._citadel (flattened/Funding.sol#1320) is not in mixedCase
Parameter Funding.initialize(address,address,address,address,address,address,uint256)._asset (flattened/Funding.sol#1321) is not in mixedCase
Parameter Funding.initialize(address,address,address,address,address,address,uint256)._xCitadel (flattened/Funding.sol#1322) is not in mixedCase
Parameter Funding.initialize(address,address,address,address,address,address,uint256)._saleRecipient (flattened/Funding.sol#1323) is not in mixedCase
Parameter Funding.initialize(address,address,address,address,address,address,uint256)._citadelPriceInAssetOracle (flattened/Funding.sol#1324) is not in mixedCase
Parameter Funding.initialize(address,address,address,address,address,address,uint256)._assetCap (flattened/Funding.sol#1325) is not in mixedCase
Parameter Funding.deposit(uint256,uint256)._assetAmountIn (flattened/Funding.sol#1372) is not in mixedCase
Parameter Funding.deposit(uint256,uint256)._minCitadelOut (flattened/Funding.sol#1372) is not in mixedCase
Parameter Funding.getAmountOut(uint256)._assetAmountIn (flattened/Funding.sol#1415) is not in mixedCase
Parameter Funding.setDiscount(uint256)._discount (flattened/Funding.sol#1457) is not in mixedCase
Parameter Funding.setAssetCap(uint256)._assetCap (flattened/Funding.sol#1483) is not in mixedCase
Parameter Funding.sweep(address)._token (flattened/Funding.sol#1507) is not in mixedCase
Parameter Funding.setDiscountLimits(uint256,uint256)._minDiscount (flattened/Funding.sol#1547) is not in mixedCase
Parameter Funding.setDiscountLimits(uint256,uint256)._maxDiscount (flattened/Funding.sol#1547) is not in mixedCase
Parameter Funding.setDiscountManager(address)._discountManager (flattened/Funding.sol#1563) is not in mixedCase
Parameter Funding.setSaleRecipient(address)._saleRecipient (flattened/Funding.sol#1573) is not in mixedCase
Parameter Funding.setCitadelAssetPriceBounds(uint256,uint256)._minPrice (flattened/Funding.sol#1587) is not in mixedCase
Parameter Funding.setCitadelAssetPriceBounds(uint256,uint256)._maxPrice (flattened/Funding.sol#1587) is not in mixedCase
Parameter Funding.updateCitadelPriceInAsset(uint256)._citadelPriceInAsset (flattened/Funding.sol#1604) is not in mixedCase
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#conformance-to-solidity-naming-conventions

Variable Funding.updateCitadelPriceInAsset(uint256)._citadelPriceInAsset (flattened/Funding.sol#1604) is too similar to Funding.xCitadelPriceInAsset (flattened/Funding.sol#1252)
Variable Funding.maxCitadelPriceInAsset (flattened/Funding.sol#1248) is too similar to Funding.minCitadelPriceInAsset (flattened/Funding.sol#1247)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#variable-names-are-too-similar

ReentrancyGuardUpgradeable.__gap (flattened/Funding.sol#749) is never used in Funding (flattened/Funding.sol#1226-1631)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-state-variable

Funding.xCitadelPriceInAsset (flattened/Funding.sol#1252) should be constant
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variables-that-could-be-declared-constant
flattened/Funding.sol analyzed (14 contracts with 77 detectors), 81 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
