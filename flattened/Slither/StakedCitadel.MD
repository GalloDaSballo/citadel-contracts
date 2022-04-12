entreprenerd@MacBook-Pro citadel-contracts % slither flattened/StakedCitadel.sol
Compilation warnings/errors on flattened/StakedCitadel.sol:
Warning: Contract code size is 32381 bytes and exceeds 24576 bytes (a limit introduced in Spurious Dragon). This contract may not be deployable on mainnet. Consider enabling the optimizer (with a low "runs" value!), turning off revert strings, or using libraries.
    --> flattened/StakedCitadel.sol:1585:1:
     |
1585 | contract StakedCitadel is
     | ^ (Relevant source part starts here and spans across multiple lines).



ERC20Upgradeable.__gap (flattened/StakedCitadel.sol#1134) shadows:
	- ContextUpgradeable.__gap (flattened/StakedCitadel.sol#747)
PausableUpgradeable.__gap (flattened/StakedCitadel.sol#1236) shadows:
	- ContextUpgradeable.__gap (flattened/StakedCitadel.sol#747)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variable-shadowing

StakedCitadel._mintSharesFor(address,uint256,uint256) (flattened/StakedCitadel.sol#2407-2419) uses a dangerous strict equality:
	- totalSupply() == 0 (flattened/StakedCitadel.sol#2413)
StakedCitadel.getPricePerFullShare() (flattened/StakedCitadel.sol#1811-1816) uses a dangerous strict equality:
	- totalSupply() == 0 (flattened/StakedCitadel.sol#1812)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dangerous-strict-equalities

Reentrancy in StakedCitadel._withdraw(uint256) (flattened/StakedCitadel.sol#2336-2364):
	External calls:
	- IStrategy(strategy).withdraw(_toWithdraw) (flattened/StakedCitadel.sol#2346)
	- IVesting(vesting).setupVesting(msg.sender,_amount,block.timestamp) (flattened/StakedCitadel.sol#2358)
	- token.safeTransfer(vesting,_amount) (flattened/StakedCitadel.sol#2359)
	State variables written after the call(s):
	- _mintSharesFor(treasury,_fee,balance().sub(_fee)) (flattened/StakedCitadel.sol#2363)
		- _balances[account] += amount (flattened/StakedCitadel.sol#1008)
	- _mintSharesFor(treasury,_fee,balance().sub(_fee)) (flattened/StakedCitadel.sol#2363)
		- _totalSupply += amount (flattened/StakedCitadel.sol#1007)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-1

StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._name (flattened/StakedCitadel.sol#1703) shadows:
	- ERC20Upgradeable._name (flattened/StakedCitadel.sol#783) (state variable)
StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._symbol (flattened/StakedCitadel.sol#1704) shadows:
	- ERC20Upgradeable._symbol (flattened/StakedCitadel.sol#784) (state variable)
StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4]).name (flattened/StakedCitadel.sol#1734) shadows:
	- ERC20Upgradeable.name() (flattened/StakedCitadel.sol#807-809) (function)
	- IERC20MetadataUpgradeable.name() (flattened/StakedCitadel.sol#623) (function)
StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4]).symbol (flattened/StakedCitadel.sol#1735) shadows:
	- ERC20Upgradeable.symbol() (flattened/StakedCitadel.sol#815-817) (function)
	- IERC20MetadataUpgradeable.symbol() (flattened/StakedCitadel.sol#628) (function)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#local-variable-shadowing

SettAccessControl.setStrategist(address)._strategist (flattened/StakedCitadel.sol#1344) lacks a zero-check on :
		- strategist = _strategist (flattened/StakedCitadel.sol#1346)
SettAccessControl.setKeeper(address)._keeper (flattened/StakedCitadel.sol#1351) lacks a zero-check on :
		- keeper = _keeper (flattened/StakedCitadel.sol#1353)
SettAccessControl.setGovernance(address)._governance (flattened/StakedCitadel.sol#1358) lacks a zero-check on :
		- governance = _governance (flattened/StakedCitadel.sol#1360)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#missing-zero-address-validation

Reentrancy in StakedCitadel._depositFor(address,uint256) (flattened/StakedCitadel.sol#2292-2305):
	External calls:
	- token.safeTransferFrom(msg.sender,address(this),_amount) (flattened/StakedCitadel.sol#2302)
	State variables written after the call(s):
	- _mintSharesFor(_recipient,_after.sub(_before),_pool) (flattened/StakedCitadel.sol#2304)
		- _balances[account] += amount (flattened/StakedCitadel.sol#1008)
	- _mintSharesFor(_recipient,_after.sub(_before),_pool) (flattened/StakedCitadel.sol#2304)
		- _totalSupply += amount (flattened/StakedCitadel.sol#1007)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-2

Reentrancy in StakedCitadel._depositFor(address,uint256) (flattened/StakedCitadel.sol#2292-2305):
	External calls:
	- token.safeTransferFrom(msg.sender,address(this),_amount) (flattened/StakedCitadel.sol#2302)
	Event emitted after the call(s):
	- Transfer(address(0),account,amount) (flattened/StakedCitadel.sol#1009)
		- _mintSharesFor(_recipient,_after.sub(_before),_pool) (flattened/StakedCitadel.sol#2304)
Reentrancy in StakedCitadel._withdraw(uint256) (flattened/StakedCitadel.sol#2336-2364):
	External calls:
	- IStrategy(strategy).withdraw(_toWithdraw) (flattened/StakedCitadel.sol#2346)
	- IVesting(vesting).setupVesting(msg.sender,_amount,block.timestamp) (flattened/StakedCitadel.sol#2358)
	- token.safeTransfer(vesting,_amount) (flattened/StakedCitadel.sol#2359)
	Event emitted after the call(s):
	- Transfer(address(0),account,amount) (flattened/StakedCitadel.sol#1009)
		- _mintSharesFor(treasury,_fee,balance().sub(_fee)) (flattened/StakedCitadel.sol#2363)
Reentrancy in StakedCitadel.reportAdditionalToken(address) (flattened/StakedCitadel.sol#1967-2004):
	External calls:
	- IERC20Upgradeable(_token).safeTransfer(treasury,governanceRewardsFee) (flattened/StakedCitadel.sol#1989)
	- IERC20Upgradeable(_token).safeTransfer(strategist,strategistRewardsFee) (flattened/StakedCitadel.sol#1990-1993)
	- IERC20Upgradeable(_token).safeTransfer(badgerTree,newBalance) (flattened/StakedCitadel.sol#1997)
	Event emitted after the call(s):
	- TreeDistribution(_token,newBalance,block.number,block.timestamp) (flattened/StakedCitadel.sol#1998-2003)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-3

StakedCitadel.getPricePerFullShare() (flattened/StakedCitadel.sol#1811-1816) uses timestamp for comparisons
	Dangerous comparisons:
	- totalSupply() == 0 (flattened/StakedCitadel.sol#1812)
StakedCitadel._withdraw(uint256) (flattened/StakedCitadel.sol#2336-2364) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(_shares != 0,0 Shares) (flattened/StakedCitadel.sol#2337)
	- b < r (flattened/StakedCitadel.sol#2344)
	- _diff < _toWithdraw (flattened/StakedCitadel.sol#2349)
StakedCitadel._mintSharesFor(address,uint256,uint256) (flattened/StakedCitadel.sol#2407-2419) uses timestamp for comparisons
	Dangerous comparisons:
	- totalSupply() == 0 (flattened/StakedCitadel.sol#2413)
StakedCitadel._handleFees(uint256,uint256) (flattened/StakedCitadel.sol#2424-2461) uses timestamp for comparisons
	Dangerous comparisons:
	- totalGovernanceFee != 0 (flattened/StakedCitadel.sol#2449)
	- feeStrategist != 0 && strategist != address(0) (flattened/StakedCitadel.sol#2453)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#block-timestamp

AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/StakedCitadel.sol#483-503) uses assembly
	- INLINE ASM (flattened/StakedCitadel.sol#495-498)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#assembly-usage

AddressUpgradeable.functionCall(address,bytes) (flattened/StakedCitadel.sol#394-396) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256) (flattened/StakedCitadel.sol#423-429) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes) (flattened/StakedCitadel.sol#456-458) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/StakedCitadel.sol#466-475) is never used and should be removed
AddressUpgradeable.sendValue(address,uint256) (flattened/StakedCitadel.sol#369-374) is never used and should be removed
ContextUpgradeable.__Context_init() (flattened/StakedCitadel.sol#729-730) is never used and should be removed
ContextUpgradeable.__Context_init_unchained() (flattened/StakedCitadel.sol#732-733) is never used and should be removed
ContextUpgradeable._msgData() (flattened/StakedCitadel.sol#738-740) is never used and should be removed
SafeERC20Upgradeable.safeApprove(IERC20Upgradeable,address,uint256) (flattened/StakedCitadel.sol#548-561) is never used and should be removed
SafeERC20Upgradeable.safeDecreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/StakedCitadel.sol#572-583) is never used and should be removed
SafeERC20Upgradeable.safeIncreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/StakedCitadel.sol#563-570) is never used and should be removed
SafeMathUpgradeable.div(uint256,uint256,string) (flattened/StakedCitadel.sol#274-283) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256) (flattened/StakedCitadel.sol#234-236) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256,string) (flattened/StakedCitadel.sol#300-309) is never used and should be removed
SafeMathUpgradeable.sub(uint256,uint256,string) (flattened/StakedCitadel.sol#251-260) is never used and should be removed
SafeMathUpgradeable.tryAdd(uint256,uint256) (flattened/StakedCitadel.sol#105-111) is never used and should be removed
SafeMathUpgradeable.tryDiv(uint256,uint256) (flattened/StakedCitadel.sol#147-152) is never used and should be removed
SafeMathUpgradeable.tryMod(uint256,uint256) (flattened/StakedCitadel.sol#159-164) is never used and should be removed
SafeMathUpgradeable.tryMul(uint256,uint256) (flattened/StakedCitadel.sol#130-140) is never used and should be removed
SafeMathUpgradeable.trySub(uint256,uint256) (flattened/StakedCitadel.sol#118-123) is never used and should be removed
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dead-code

Pragma version0.8.12 (flattened/StakedCitadel.sol#2) necessitates a version too recent to be trusted. Consider deploying with 0.6.12/0.7.6/0.8.7
solc-0.8.12 is not recommended for deployment
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#incorrect-versions-of-solidity

Low level call in AddressUpgradeable.sendValue(address,uint256) (flattened/StakedCitadel.sol#369-374):
	- (success) = recipient.call{value: amount}() (flattened/StakedCitadel.sol#372)
Low level call in AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/StakedCitadel.sol#437-448):
	- (success,returndata) = target.call{value: value}(data) (flattened/StakedCitadel.sol#446)
Low level call in AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/StakedCitadel.sol#466-475):
	- (success,returndata) = target.staticcall(data) (flattened/StakedCitadel.sol#473)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#low-level-calls

Function ContextUpgradeable.__Context_init() (flattened/StakedCitadel.sol#729-730) is not in mixedCase
Function ContextUpgradeable.__Context_init_unchained() (flattened/StakedCitadel.sol#732-733) is not in mixedCase
Variable ContextUpgradeable.__gap (flattened/StakedCitadel.sol#747) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init(string,string) (flattened/StakedCitadel.sol#795-797) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init_unchained(string,string) (flattened/StakedCitadel.sol#799-802) is not in mixedCase
Variable ERC20Upgradeable.__gap (flattened/StakedCitadel.sol#1134) is not in mixedCase
Function PausableUpgradeable.__Pausable_init() (flattened/StakedCitadel.sol#1168-1170) is not in mixedCase
Function PausableUpgradeable.__Pausable_init_unchained() (flattened/StakedCitadel.sol#1172-1174) is not in mixedCase
Variable PausableUpgradeable.__gap (flattened/StakedCitadel.sol#1236) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init() (flattened/StakedCitadel.sol#1276-1278) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init_unchained() (flattened/StakedCitadel.sol#1280-1282) is not in mixedCase
Variable ReentrancyGuardUpgradeable.__gap (flattened/StakedCitadel.sol#1310) is not in mixedCase
Parameter SettAccessControl.setStrategist(address)._strategist (flattened/StakedCitadel.sol#1344) is not in mixedCase
Parameter SettAccessControl.setKeeper(address)._keeper (flattened/StakedCitadel.sol#1351) is not in mixedCase
Parameter SettAccessControl.setGovernance(address)._governance (flattened/StakedCitadel.sol#1358) is not in mixedCase
Variable SettAccessControl.__gap (flattened/StakedCitadel.sol#1363) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._token (flattened/StakedCitadel.sol#1695) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._governance (flattened/StakedCitadel.sol#1696) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._keeper (flattened/StakedCitadel.sol#1697) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._guardian (flattened/StakedCitadel.sol#1698) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._treasury (flattened/StakedCitadel.sol#1699) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._strategist (flattened/StakedCitadel.sol#1700) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._badgerTree (flattened/StakedCitadel.sol#1701) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._vesting (flattened/StakedCitadel.sol#1702) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._name (flattened/StakedCitadel.sol#1703) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._symbol (flattened/StakedCitadel.sol#1704) is not in mixedCase
Parameter StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4])._feeConfig (flattened/StakedCitadel.sol#1705) is not in mixedCase
Parameter StakedCitadel.deposit(uint256)._amount (flattened/StakedCitadel.sol#1837) is not in mixedCase
Parameter StakedCitadel.deposit(uint256,bytes32[])._amount (flattened/StakedCitadel.sol#1847) is not in mixedCase
Parameter StakedCitadel.depositFor(address,uint256)._recipient (flattened/StakedCitadel.sol#1878) is not in mixedCase
Parameter StakedCitadel.depositFor(address,uint256)._amount (flattened/StakedCitadel.sol#1878) is not in mixedCase
Parameter StakedCitadel.depositFor(address,uint256,bytes32[])._recipient (flattened/StakedCitadel.sol#1892) is not in mixedCase
Parameter StakedCitadel.depositFor(address,uint256,bytes32[])._amount (flattened/StakedCitadel.sol#1893) is not in mixedCase
Parameter StakedCitadel.withdraw(uint256)._shares (flattened/StakedCitadel.sol#1903) is not in mixedCase
Parameter StakedCitadel.reportHarvest(uint256)._harvestedAmount (flattened/StakedCitadel.sol#1924) is not in mixedCase
Parameter StakedCitadel.reportAdditionalToken(address)._token (flattened/StakedCitadel.sol#1967) is not in mixedCase
Parameter StakedCitadel.setTreasury(address)._treasury (flattened/StakedCitadel.sol#2013) is not in mixedCase
Parameter StakedCitadel.setStrategy(address)._strategy (flattened/StakedCitadel.sol#2028) is not in mixedCase
Parameter StakedCitadel.setMaxWithdrawalFee(uint256)._fees (flattened/StakedCitadel.sol#2049) is not in mixedCase
Parameter StakedCitadel.setMaxPerformanceFee(uint256)._fees (flattened/StakedCitadel.sol#2061) is not in mixedCase
Parameter StakedCitadel.setMaxManagementFee(uint256)._fees (flattened/StakedCitadel.sol#2076) is not in mixedCase
Parameter StakedCitadel.setGuardian(address)._guardian (flattened/StakedCitadel.sol#2088) is not in mixedCase
Parameter StakedCitadel.setVesting(address)._vesting (flattened/StakedCitadel.sol#2100) is not in mixedCase
Parameter StakedCitadel.setToEarnBps(uint256)._newToEarnBps (flattened/StakedCitadel.sol#2114) is not in mixedCase
Parameter StakedCitadel.setGuestList(address)._guestList (flattened/StakedCitadel.sol#2127) is not in mixedCase
Parameter StakedCitadel.setWithdrawalFee(uint256)._withdrawalFee (flattened/StakedCitadel.sol#2139) is not in mixedCase
Parameter StakedCitadel.setPerformanceFeeStrategist(uint256)._performanceFeeStrategist (flattened/StakedCitadel.sol#2153) is not in mixedCase
Parameter StakedCitadel.setPerformanceFeeGovernance(uint256)._performanceFeeGovernance (flattened/StakedCitadel.sol#2173) is not in mixedCase
Parameter StakedCitadel.setManagementFee(uint256)._fees (flattened/StakedCitadel.sol#2192) is not in mixedCase
Parameter StakedCitadel.emitNonProtectedToken(address)._token (flattened/StakedCitadel.sol#2215) is not in mixedCase
Parameter StakedCitadel.sweepExtraToken(address)._token (flattened/StakedCitadel.sol#2226) is not in mixedCase
Constant StakedCitadel._defaultNamePrefix (flattened/StakedCitadel.sol#1612) is not in UPPER_CASE_WITH_UNDERSCORES
Constant StakedCitadel._symbolSymbolPrefix (flattened/StakedCitadel.sol#1613) is not in UPPER_CASE_WITH_UNDERSCORES
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#conformance-to-solidity-naming-conventions

ReentrancyGuardUpgradeable.__gap (flattened/StakedCitadel.sol#1310) is never used in StakedCitadel (flattened/StakedCitadel.sol#1585-2463)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-state-variable

name() should be declared external:
	- ERC20Upgradeable.name() (flattened/StakedCitadel.sol#807-809)
symbol() should be declared external:
	- ERC20Upgradeable.symbol() (flattened/StakedCitadel.sol#815-817)
decimals() should be declared external:
	- ERC20Upgradeable.decimals() (flattened/StakedCitadel.sol#832-834)
transfer(address,uint256) should be declared external:
	- ERC20Upgradeable.transfer(address,uint256) (flattened/StakedCitadel.sol#858-862)
approve(address,uint256) should be declared external:
	- ERC20Upgradeable.approve(address,uint256) (flattened/StakedCitadel.sol#881-885)
transferFrom(address,address,uint256) should be declared external:
	- ERC20Upgradeable.transferFrom(address,address,uint256) (flattened/StakedCitadel.sol#903-912)
increaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.increaseAllowance(address,uint256) (flattened/StakedCitadel.sol#926-930)
decreaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.decreaseAllowance(address,uint256) (flattened/StakedCitadel.sol#946-955)
setGovernance(address) should be declared external:
	- SettAccessControl.setGovernance(address) (flattened/StakedCitadel.sol#1358-1361)
initialize(address,address,address,address,address,address,address,address,string,string,uint256[4]) should be declared external:
	- StakedCitadel.initialize(address,address,address,address,address,address,address,address,string,string,uint256[4]) (flattened/StakedCitadel.sol#1694-1783)
getPricePerFullShare() should be declared external:
	- StakedCitadel.getPricePerFullShare() (flattened/StakedCitadel.sol#1811-1816)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#public-function-that-could-be-declared-external
flattened/StakedCitadel.sol analyzed (17 contracts with 77 detectors), 111 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
