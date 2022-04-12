entreprenerd@MacBook-Pro citadel-contracts % slither flattened/CitadelMinter.sol 

Reentrancy in CitadelMinter.mintAndDistribute() (flattened/CitadelMinter.sol#1842-1915):
	External calls:
	- citadelToken.mint(address(this),mintable) (flattened/CitadelMinter.sol#1851)
	- IVault(cachedXCitadel).deposit(lockingAmount) (flattened/CitadelMinter.sol#1868)
	- xCitadelLocker.notifyRewardAmount(address(cachedXCitadel),xCitadelToLockers) (flattened/CitadelMinter.sol#1874-1877)
	- citadelToken.transfer(address(cachedXCitadel),stakingAmount) (flattened/CitadelMinter.sol#1890)
	- _transferToFundingPools(fundingAmount) (flattened/CitadelMinter.sol#1904)
		- returndata = address(token).functionCall(data,SafeERC20: low-level call failed) (flattened/CitadelMinter.sol#372)
		- (success,returndata) = target.call{value: value}(data) (flattened/CitadelMinter.sol#222)
		- IERC20Upgradeable(address(citadelToken)).safeTransfer(pool,amount) (flattened/CitadelMinter.sol#2028)
	External calls sending eth:
	- _transferToFundingPools(fundingAmount) (flattened/CitadelMinter.sol#1904)
		- (success,returndata) = target.call{value: value}(data) (flattened/CitadelMinter.sol#222)
	State variables written after the call(s):
	- lastMintTimestamp = block.timestamp (flattened/CitadelMinter.sol#1914)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities

ERC20Upgradeable.__gap (flattened/CitadelMinter.sol#910) shadows:
	- ContextUpgradeable.__gap (flattened/CitadelMinter.sol#523)
PausableUpgradeable.__gap (flattened/CitadelMinter.sol#1443) shadows:
	- ContextUpgradeable.__gap (flattened/CitadelMinter.sol#523)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variable-shadowing

CitadelMinter.mintAndDistribute() (flattened/CitadelMinter.sol#1842-1915) ignores return value by citadelToken.transfer(address(cachedXCitadel),stakingAmount) (flattened/CitadelMinter.sol#1890)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unchecked-transfer

CitadelMinter.initializeLastMintTimestamp() (flattened/CitadelMinter.sol#1992-2009) contains a tautology or contradiction:
	- require(bool,string)(globalStartTimestamp >= 0,CitadelMinter: supply schedule start not initialized) (flattened/CitadelMinter.sol#2004-2007)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#tautology-or-contradiction

CitadelMinter._transferToFundingPools(uint256).i (flattened/CitadelMinter.sol#2022) is a local variable never initialized
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#uninitialized-local-variables

CitadelMinter.initialize(address,address,address,address,address) (flattened/CitadelMinter.sol#1784-1810) ignores return value by citadelToken.approve(_xCitadel,type()(uint256).max) (flattened/CitadelMinter.sol#1807)
CitadelMinter.initialize(address,address,address,address,address) (flattened/CitadelMinter.sol#1784-1810) ignores return value by xCitadel.approve(_xCitadelLocker,type()(uint256).max) (flattened/CitadelMinter.sol#1809)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-return

Reentrancy in CitadelMinter._transferToFundingPools(uint256) (flattened/CitadelMinter.sol#2016-2037):
	External calls:
	- IERC20Upgradeable(address(citadelToken)).safeTransfer(pool,amount) (flattened/CitadelMinter.sol#2028)
	Event emitted after the call(s):
	- CitadelDistributionToFundingPool(lastMintTimestamp,block.timestamp,pool,amount) (flattened/CitadelMinter.sol#2030-2035)
Reentrancy in CitadelMinter.mintAndDistribute() (flattened/CitadelMinter.sol#1842-1915):
	External calls:
	- citadelToken.mint(address(this),mintable) (flattened/CitadelMinter.sol#1851)
	- IVault(cachedXCitadel).deposit(lockingAmount) (flattened/CitadelMinter.sol#1868)
	- xCitadelLocker.notifyRewardAmount(address(cachedXCitadel),xCitadelToLockers) (flattened/CitadelMinter.sol#1874-1877)
	Event emitted after the call(s):
	- CitadelDistributionToLocking(cachedLastMintTimestamp,block.timestamp,lockingAmount,xCitadelToLockers) (flattened/CitadelMinter.sol#1878-1883)
Reentrancy in CitadelMinter.mintAndDistribute() (flattened/CitadelMinter.sol#1842-1915):
	External calls:
	- citadelToken.mint(address(this),mintable) (flattened/CitadelMinter.sol#1851)
	- IVault(cachedXCitadel).deposit(lockingAmount) (flattened/CitadelMinter.sol#1868)
	- xCitadelLocker.notifyRewardAmount(address(cachedXCitadel),xCitadelToLockers) (flattened/CitadelMinter.sol#1874-1877)
	- citadelToken.transfer(address(cachedXCitadel),stakingAmount) (flattened/CitadelMinter.sol#1890)
	Event emitted after the call(s):
	- CitadelDistributionToStaking(cachedLastMintTimestamp,block.timestamp,stakingAmount) (flattened/CitadelMinter.sol#1891-1895)
Reentrancy in CitadelMinter.mintAndDistribute() (flattened/CitadelMinter.sol#1842-1915):
	External calls:
	- citadelToken.mint(address(this),mintable) (flattened/CitadelMinter.sol#1851)
	- IVault(cachedXCitadel).deposit(lockingAmount) (flattened/CitadelMinter.sol#1868)
	- xCitadelLocker.notifyRewardAmount(address(cachedXCitadel),xCitadelToLockers) (flattened/CitadelMinter.sol#1874-1877)
	- citadelToken.transfer(address(cachedXCitadel),stakingAmount) (flattened/CitadelMinter.sol#1890)
	- _transferToFundingPools(fundingAmount) (flattened/CitadelMinter.sol#1904)
		- returndata = address(token).functionCall(data,SafeERC20: low-level call failed) (flattened/CitadelMinter.sol#372)
		- (success,returndata) = target.call{value: value}(data) (flattened/CitadelMinter.sol#222)
		- IERC20Upgradeable(address(citadelToken)).safeTransfer(pool,amount) (flattened/CitadelMinter.sol#2028)
	External calls sending eth:
	- _transferToFundingPools(fundingAmount) (flattened/CitadelMinter.sol#1904)
		- (success,returndata) = target.call{value: value}(data) (flattened/CitadelMinter.sol#222)
	Event emitted after the call(s):
	- CitadelDistribution(fundingAmount,stakingAmount,lockingAmount) (flattened/CitadelMinter.sol#1912)
	- CitadelDistributionToFunding(cachedLastMintTimestamp,block.timestamp,fundingAmount) (flattened/CitadelMinter.sol#1905-1909)
	- CitadelDistributionToFundingPool(lastMintTimestamp,block.timestamp,pool,amount) (flattened/CitadelMinter.sol#2030-2035)
		- _transferToFundingPools(fundingAmount) (flattened/CitadelMinter.sol#1904)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-3

CitadelMinter.initializeLastMintTimestamp() (flattened/CitadelMinter.sol#1992-2009) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(lastMintTimestamp == 0,CitadelMinter: last mint timestamp already initialized) (flattened/CitadelMinter.sol#1997-2000)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#block-timestamp

AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/CitadelMinter.sol#259-279) uses assembly
	- INLINE ASM (flattened/CitadelMinter.sol#271-274)
EnumerableSetUpgradeable.values(EnumerableSetUpgradeable.AddressSet) (flattened/CitadelMinter.sol#1258-1267) uses assembly
	- INLINE ASM (flattened/CitadelMinter.sol#1262-1264)
EnumerableSetUpgradeable.values(EnumerableSetUpgradeable.UintSet) (flattened/CitadelMinter.sol#1331-1340) uses assembly
	- INLINE ASM (flattened/CitadelMinter.sol#1335-1337)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#assembly-usage

GlobalAccessControlManaged.gacPausable() (flattened/CitadelMinter.sol#1533-1537) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/CitadelMinter.sol#1534)
GlobalAccessControlManaged.gacPausable() (flattened/CitadelMinter.sol#1533-1537) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/CitadelMinter.sol#1535)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality

AddressUpgradeable.functionCall(address,bytes) (flattened/CitadelMinter.sol#170-172) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256) (flattened/CitadelMinter.sol#199-205) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes) (flattened/CitadelMinter.sol#232-234) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/CitadelMinter.sol#242-251) is never used and should be removed
AddressUpgradeable.sendValue(address,uint256) (flattened/CitadelMinter.sol#145-150) is never used and should be removed
ContextUpgradeable.__Context_init() (flattened/CitadelMinter.sol#505-506) is never used and should be removed
ContextUpgradeable.__Context_init_unchained() (flattened/CitadelMinter.sol#508-509) is never used and should be removed
ContextUpgradeable._msgData() (flattened/CitadelMinter.sol#514-516) is never used and should be removed
ERC20Upgradeable.__ERC20_init(string,string) (flattened/CitadelMinter.sol#571-573) is never used and should be removed
ERC20Upgradeable.__ERC20_init_unchained(string,string) (flattened/CitadelMinter.sol#575-578) is never used and should be removed
ERC20Upgradeable._burn(address,uint256) (flattened/CitadelMinter.sol#801-816) is never used and should be removed
ERC20Upgradeable._mint(address,uint256) (flattened/CitadelMinter.sol#778-788) is never used and should be removed
EnumerableSetUpgradeable._values(EnumerableSetUpgradeable.Set) (flattened/CitadelMinter.sol#1126-1128) is never used and should be removed
EnumerableSetUpgradeable.add(EnumerableSetUpgradeable.Bytes32Set,bytes32) (flattened/CitadelMinter.sol#1142-1144) is never used and should be removed
EnumerableSetUpgradeable.add(EnumerableSetUpgradeable.UintSet,uint256) (flattened/CitadelMinter.sol#1281-1283) is never used and should be removed
EnumerableSetUpgradeable.at(EnumerableSetUpgradeable.Bytes32Set,uint256) (flattened/CitadelMinter.sol#1180-1182) is never used and should be removed
EnumerableSetUpgradeable.at(EnumerableSetUpgradeable.UintSet,uint256) (flattened/CitadelMinter.sol#1319-1321) is never used and should be removed
EnumerableSetUpgradeable.contains(EnumerableSetUpgradeable.Bytes32Set,bytes32) (flattened/CitadelMinter.sol#1159-1161) is never used and should be removed
EnumerableSetUpgradeable.contains(EnumerableSetUpgradeable.UintSet,uint256) (flattened/CitadelMinter.sol#1298-1300) is never used and should be removed
EnumerableSetUpgradeable.length(EnumerableSetUpgradeable.Bytes32Set) (flattened/CitadelMinter.sol#1166-1168) is never used and should be removed
EnumerableSetUpgradeable.length(EnumerableSetUpgradeable.UintSet) (flattened/CitadelMinter.sol#1305-1307) is never used and should be removed
EnumerableSetUpgradeable.remove(EnumerableSetUpgradeable.Bytes32Set,bytes32) (flattened/CitadelMinter.sol#1152-1154) is never used and should be removed
EnumerableSetUpgradeable.remove(EnumerableSetUpgradeable.UintSet,uint256) (flattened/CitadelMinter.sol#1291-1293) is never used and should be removed
EnumerableSetUpgradeable.values(EnumerableSetUpgradeable.AddressSet) (flattened/CitadelMinter.sol#1258-1267) is never used and should be removed
EnumerableSetUpgradeable.values(EnumerableSetUpgradeable.Bytes32Set) (flattened/CitadelMinter.sol#1192-1194) is never used and should be removed
EnumerableSetUpgradeable.values(EnumerableSetUpgradeable.UintSet) (flattened/CitadelMinter.sol#1331-1340) is never used and should be removed
PausableUpgradeable.__Pausable_init() (flattened/CitadelMinter.sol#1375-1377) is never used and should be removed
SafeERC20Upgradeable.safeApprove(IERC20Upgradeable,address,uint256) (flattened/CitadelMinter.sol#324-337) is never used and should be removed
SafeERC20Upgradeable.safeDecreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/CitadelMinter.sol#348-359) is never used and should be removed
SafeERC20Upgradeable.safeIncreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/CitadelMinter.sol#339-346) is never used and should be removed
SafeERC20Upgradeable.safeTransferFrom(IERC20Upgradeable,address,address,uint256) (flattened/CitadelMinter.sol#308-315) is never used and should be removed
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dead-code

Pragma version0.8.12 (flattened/CitadelMinter.sol#3) necessitates a version too recent to be trusted. Consider deploying with 0.6.12/0.7.6/0.8.7
solc-0.8.12 is not recommended for deployment
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#incorrect-versions-of-solidity

Low level call in AddressUpgradeable.sendValue(address,uint256) (flattened/CitadelMinter.sol#145-150):
	- (success) = recipient.call{value: amount}() (flattened/CitadelMinter.sol#148)
Low level call in AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/CitadelMinter.sol#213-224):
	- (success,returndata) = target.call{value: value}(data) (flattened/CitadelMinter.sol#222)
Low level call in AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/CitadelMinter.sol#242-251):
	- (success,returndata) = target.staticcall(data) (flattened/CitadelMinter.sol#249)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#low-level-calls

Function ContextUpgradeable.__Context_init() (flattened/CitadelMinter.sol#505-506) is not in mixedCase
Function ContextUpgradeable.__Context_init_unchained() (flattened/CitadelMinter.sol#508-509) is not in mixedCase
Variable ContextUpgradeable.__gap (flattened/CitadelMinter.sol#523) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init(string,string) (flattened/CitadelMinter.sol#571-573) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init_unchained(string,string) (flattened/CitadelMinter.sol#575-578) is not in mixedCase
Variable ERC20Upgradeable.__gap (flattened/CitadelMinter.sol#910) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init() (flattened/CitadelMinter.sol#950-952) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init_unchained() (flattened/CitadelMinter.sol#954-956) is not in mixedCase
Variable ReentrancyGuardUpgradeable.__gap (flattened/CitadelMinter.sol#984) is not in mixedCase
Function PausableUpgradeable.__Pausable_init() (flattened/CitadelMinter.sol#1375-1377) is not in mixedCase
Function PausableUpgradeable.__Pausable_init_unchained() (flattened/CitadelMinter.sol#1379-1381) is not in mixedCase
Variable PausableUpgradeable.__gap (flattened/CitadelMinter.sol#1443) is not in mixedCase
Function GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address) (flattened/CitadelMinter.sol#1490-1496) is not in mixedCase
Parameter GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address)._globalAccessControl (flattened/CitadelMinter.sol#1490) is not in mixedCase
Parameter CitadelMinter.initialize(address,address,address,address,address)._gac (flattened/CitadelMinter.sol#1785) is not in mixedCase
Parameter CitadelMinter.initialize(address,address,address,address,address)._citadelToken (flattened/CitadelMinter.sol#1786) is not in mixedCase
Parameter CitadelMinter.initialize(address,address,address,address,address)._xCitadel (flattened/CitadelMinter.sol#1787) is not in mixedCase
Parameter CitadelMinter.initialize(address,address,address,address,address)._xCitadelLocker (flattened/CitadelMinter.sol#1788) is not in mixedCase
Parameter CitadelMinter.initialize(address,address,address,address,address)._supplySchedule (flattened/CitadelMinter.sol#1789) is not in mixedCase
Parameter CitadelMinter.setFundingPoolWeight(address,uint256)._pool (flattened/CitadelMinter.sol#1924) is not in mixedCase
Parameter CitadelMinter.setFundingPoolWeight(address,uint256)._weight (flattened/CitadelMinter.sol#1924) is not in mixedCase
Parameter CitadelMinter.setCitadelDistributionSplit(uint256,uint256,uint256)._fundingBps (flattened/CitadelMinter.sol#1973) is not in mixedCase
Parameter CitadelMinter.setCitadelDistributionSplit(uint256,uint256,uint256)._stakingBps (flattened/CitadelMinter.sol#1974) is not in mixedCase
Parameter CitadelMinter.setCitadelDistributionSplit(uint256,uint256,uint256)._lockingBps (flattened/CitadelMinter.sol#1975) is not in mixedCase
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#conformance-to-solidity-naming-conventions

ERC20Upgradeable.__gap (flattened/CitadelMinter.sol#910) is never used in ERC20Upgradeable (flattened/CitadelMinter.sol#552-911)
ReentrancyGuardUpgradeable.__gap (flattened/CitadelMinter.sol#984) is never used in CitadelMinter (flattened/CitadelMinter.sol#1698-2052)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-state-variable

name() should be declared external:
	- ERC20Upgradeable.name() (flattened/CitadelMinter.sol#583-585)
symbol() should be declared external:
	- ERC20Upgradeable.symbol() (flattened/CitadelMinter.sol#591-593)
decimals() should be declared external:
	- ERC20Upgradeable.decimals() (flattened/CitadelMinter.sol#608-610)
totalSupply() should be declared external:
	- ERC20Upgradeable.totalSupply() (flattened/CitadelMinter.sol#615-617)
balanceOf(address) should be declared external:
	- ERC20Upgradeable.balanceOf(address) (flattened/CitadelMinter.sol#622-624)
transfer(address,uint256) should be declared external:
	- ERC20Upgradeable.transfer(address,uint256) (flattened/CitadelMinter.sol#634-638)
approve(address,uint256) should be declared external:
	- ERC20Upgradeable.approve(address,uint256) (flattened/CitadelMinter.sol#657-661)
transferFrom(address,address,uint256) should be declared external:
	- ERC20Upgradeable.transferFrom(address,address,uint256) (flattened/CitadelMinter.sol#679-688)
increaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.increaseAllowance(address,uint256) (flattened/CitadelMinter.sol#702-706)
decreaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.decreaseAllowance(address,uint256) (flattened/CitadelMinter.sol#722-731)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#public-function-that-could-be-declared-external
flattened/CitadelMinter.sol analyzed (18 contracts with 77 detectors), 90 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
