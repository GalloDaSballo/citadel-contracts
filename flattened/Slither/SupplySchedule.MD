entreprenerd@MacBook-Pro citadel-contracts % slither flattened/SupplySchedule.sol     

ERC20Upgradeable.__gap (flattened/SupplySchedule.sol#1242) shadows:
	- ContextUpgradeable.__gap (flattened/SupplySchedule.sol#855)
PausableUpgradeable.__gap (flattened/SupplySchedule.sol#1613) shadows:
	- ContextUpgradeable.__gap (flattened/SupplySchedule.sol#855)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variable-shadowing

SupplySchedule.getMintable(uint256) (flattened/SupplySchedule.sol#2092-2131) performs a multiplication on the result of a division:
	-startingEpoch = (lastMintTimestamp - globalStartTimestamp) / epochLength (flattened/SupplySchedule.sol#2112-2113)
	-i = startingEpoch (flattened/SupplySchedule.sol#2118)
	-epochStartTime = globalStartTimestamp + i * epochLength (flattened/SupplySchedule.sol#2121)
SupplySchedule.getMintableDebug(uint256) (flattened/SupplySchedule.sol#2183-2238) performs a multiplication on the result of a division:
	-startingEpoch = (lastMintTimestamp - globalStartTimestamp) / epochLength (flattened/SupplySchedule.sol#2205-2206)
	-i = startingEpoch (flattened/SupplySchedule.sol#2213)
	-epochStartTime = globalStartTimestamp + i * epochLength (flattened/SupplySchedule.sol#2216)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#divide-before-multiply

SupplySchedule.setMintingStart(uint256) (flattened/SupplySchedule.sol#2137-2153) contains a tautology or contradiction:
	- require(bool,string)(_globalStartTimestamp >= 0,SupplySchedule: minting must start at or after current time) (flattened/SupplySchedule.sol#2146-2149)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#tautology-or-contradiction

SupplySchedule.getMintable(uint256) (flattened/SupplySchedule.sol#2092-2131) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(block.timestamp > lastMintTimestamp,SupplySchedule: already minted up to current block) (flattened/SupplySchedule.sol#2101-2104)
	- i <= endingEpoch (flattened/SupplySchedule.sol#2118)
SupplySchedule.getMintableDebug(uint256) (flattened/SupplySchedule.sol#2183-2238) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(block.timestamp > lastMintTimestamp,SupplySchedule: already minted up to current block) (flattened/SupplySchedule.sol#2192-2195)
	- i <= endingEpoch (flattened/SupplySchedule.sol#2213)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#block-timestamp

AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/SupplySchedule.sol#729-749) uses assembly
	- INLINE ASM (flattened/SupplySchedule.sol#741-744)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#assembly-usage

GlobalAccessControlManaged.gacPausable() (flattened/SupplySchedule.sol#2004-2008) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/SupplySchedule.sol#2006)
GlobalAccessControlManaged.gacPausable() (flattened/SupplySchedule.sol#2004-2008) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/SupplySchedule.sol#2005)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality

AddressUpgradeable.functionCall(address,bytes) (flattened/SupplySchedule.sol#640-642) is never used and should be removed
AddressUpgradeable.functionCall(address,bytes,string) (flattened/SupplySchedule.sol#650-656) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256) (flattened/SupplySchedule.sol#669-675) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/SupplySchedule.sol#683-694) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes) (flattened/SupplySchedule.sol#702-704) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/SupplySchedule.sol#712-721) is never used and should be removed
AddressUpgradeable.sendValue(address,uint256) (flattened/SupplySchedule.sol#615-620) is never used and should be removed
AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/SupplySchedule.sol#729-749) is never used and should be removed
ContextUpgradeable.__Context_init() (flattened/SupplySchedule.sol#837-838) is never used and should be removed
ContextUpgradeable.__Context_init_unchained() (flattened/SupplySchedule.sol#840-841) is never used and should be removed
ContextUpgradeable._msgData() (flattened/SupplySchedule.sol#846-848) is never used and should be removed
DSTest.assertEq(address,address) (flattened/SupplySchedule.sol#73-80) is never used and should be removed
DSTest.assertEq(address,address,string) (flattened/SupplySchedule.sol#81-86) is never used and should be removed
DSTest.assertEq(bytes32,bytes32) (flattened/SupplySchedule.sol#88-95) is never used and should be removed
DSTest.assertEq(bytes32,bytes32,string) (flattened/SupplySchedule.sol#96-101) is never used and should be removed
DSTest.assertEq(int256,int256) (flattened/SupplySchedule.sol#109-116) is never used and should be removed
DSTest.assertEq(int256,int256,string) (flattened/SupplySchedule.sol#117-122) is never used and should be removed
DSTest.assertEq(string,string) (flattened/SupplySchedule.sol#394-401) is never used and should be removed
DSTest.assertEq(string,string,string) (flattened/SupplySchedule.sol#402-407) is never used and should be removed
DSTest.assertEq(uint256,uint256) (flattened/SupplySchedule.sol#123-130) is never used and should be removed
DSTest.assertEq(uint256,uint256,string) (flattened/SupplySchedule.sol#131-136) is never used and should be removed
DSTest.assertEq0(bytes,bytes) (flattened/SupplySchedule.sol#421-428) is never used and should be removed
DSTest.assertEq0(bytes,bytes,string) (flattened/SupplySchedule.sol#429-434) is never used and should be removed
DSTest.assertEq32(bytes32,bytes32) (flattened/SupplySchedule.sol#102-104) is never used and should be removed
DSTest.assertEq32(bytes32,bytes32,string) (flattened/SupplySchedule.sol#105-107) is never used and should be removed
DSTest.assertEqDecimal(int256,int256,uint256) (flattened/SupplySchedule.sol#137-144) is never used and should be removed
DSTest.assertEqDecimal(int256,int256,uint256,string) (flattened/SupplySchedule.sol#145-150) is never used and should be removed
DSTest.assertEqDecimal(uint256,uint256,uint256) (flattened/SupplySchedule.sol#151-158) is never used and should be removed
DSTest.assertEqDecimal(uint256,uint256,uint256,string) (flattened/SupplySchedule.sol#159-164) is never used and should be removed
DSTest.assertGe(int256,int256) (flattened/SupplySchedule.sol#237-244) is never used and should be removed
DSTest.assertGe(int256,int256,string) (flattened/SupplySchedule.sol#245-250) is never used and should be removed
DSTest.assertGe(uint256,uint256) (flattened/SupplySchedule.sol#223-230) is never used and should be removed
DSTest.assertGe(uint256,uint256,string) (flattened/SupplySchedule.sol#231-236) is never used and should be removed
DSTest.assertGeDecimal(int256,int256,uint256) (flattened/SupplySchedule.sol#251-258) is never used and should be removed
DSTest.assertGeDecimal(int256,int256,uint256,string) (flattened/SupplySchedule.sol#259-264) is never used and should be removed
DSTest.assertGeDecimal(uint256,uint256,uint256) (flattened/SupplySchedule.sol#265-272) is never used and should be removed
DSTest.assertGeDecimal(uint256,uint256,uint256,string) (flattened/SupplySchedule.sol#273-278) is never used and should be removed
DSTest.assertGt(int256,int256) (flattened/SupplySchedule.sol#180-187) is never used and should be removed
DSTest.assertGt(int256,int256,string) (flattened/SupplySchedule.sol#188-193) is never used and should be removed
DSTest.assertGt(uint256,uint256) (flattened/SupplySchedule.sol#166-173) is never used and should be removed
DSTest.assertGt(uint256,uint256,string) (flattened/SupplySchedule.sol#174-179) is never used and should be removed
DSTest.assertGtDecimal(int256,int256,uint256) (flattened/SupplySchedule.sol#194-201) is never used and should be removed
DSTest.assertGtDecimal(int256,int256,uint256,string) (flattened/SupplySchedule.sol#202-207) is never used and should be removed
DSTest.assertGtDecimal(uint256,uint256,uint256) (flattened/SupplySchedule.sol#208-215) is never used and should be removed
DSTest.assertGtDecimal(uint256,uint256,uint256,string) (flattened/SupplySchedule.sol#216-221) is never used and should be removed
DSTest.assertLe(int256,int256) (flattened/SupplySchedule.sol#351-358) is never used and should be removed
DSTest.assertLe(int256,int256,string) (flattened/SupplySchedule.sol#359-364) is never used and should be removed
DSTest.assertLe(uint256,uint256) (flattened/SupplySchedule.sol#337-344) is never used and should be removed
DSTest.assertLe(uint256,uint256,string) (flattened/SupplySchedule.sol#345-350) is never used and should be removed
DSTest.assertLeDecimal(int256,int256,uint256) (flattened/SupplySchedule.sol#365-372) is never used and should be removed
DSTest.assertLeDecimal(int256,int256,uint256,string) (flattened/SupplySchedule.sol#373-378) is never used and should be removed
DSTest.assertLeDecimal(uint256,uint256,uint256) (flattened/SupplySchedule.sol#379-386) is never used and should be removed
DSTest.assertLeDecimal(uint256,uint256,uint256,string) (flattened/SupplySchedule.sol#387-392) is never used and should be removed
DSTest.assertLt(int256,int256) (flattened/SupplySchedule.sol#294-301) is never used and should be removed
DSTest.assertLt(int256,int256,string) (flattened/SupplySchedule.sol#302-307) is never used and should be removed
DSTest.assertLt(uint256,uint256) (flattened/SupplySchedule.sol#280-287) is never used and should be removed
DSTest.assertLt(uint256,uint256,string) (flattened/SupplySchedule.sol#288-293) is never used and should be removed
DSTest.assertLtDecimal(int256,int256,uint256) (flattened/SupplySchedule.sol#308-315) is never used and should be removed
DSTest.assertLtDecimal(int256,int256,uint256,string) (flattened/SupplySchedule.sol#316-321) is never used and should be removed
DSTest.assertLtDecimal(uint256,uint256,uint256) (flattened/SupplySchedule.sol#322-329) is never used and should be removed
DSTest.assertLtDecimal(uint256,uint256,uint256,string) (flattened/SupplySchedule.sol#330-335) is never used and should be removed
DSTest.assertTrue(bool) (flattened/SupplySchedule.sol#59-64) is never used and should be removed
DSTest.assertTrue(bool,string) (flattened/SupplySchedule.sol#66-71) is never used and should be removed
DSTest.checkEq0(bytes,bytes) (flattened/SupplySchedule.sol#409-420) is never used and should be removed
DSTest.fail() (flattened/SupplySchedule.sol#48-50) is never used and should be removed
ERC20Upgradeable.__ERC20_init(string,string) (flattened/SupplySchedule.sol#903-905) is never used and should be removed
ERC20Upgradeable.__ERC20_init_unchained(string,string) (flattened/SupplySchedule.sol#907-910) is never used and should be removed
ERC20Upgradeable._burn(address,uint256) (flattened/SupplySchedule.sol#1133-1148) is never used and should be removed
ERC20Upgradeable._mint(address,uint256) (flattened/SupplySchedule.sol#1110-1120) is never used and should be removed
MathUpgradeable.average(uint256,uint256) (flattened/SupplySchedule.sol#1270-1273) is never used and should be removed
MathUpgradeable.ceilDiv(uint256,uint256) (flattened/SupplySchedule.sol#1281-1284) is never used and should be removed
PausableUpgradeable.__Pausable_init() (flattened/SupplySchedule.sol#1545-1547) is never used and should be removed
ReentrancyGuardUpgradeable.__ReentrancyGuard_init() (flattened/SupplySchedule.sol#1751-1753) is never used and should be removed
ReentrancyGuardUpgradeable.__ReentrancyGuard_init_unchained() (flattened/SupplySchedule.sol#1755-1757) is never used and should be removed
SafeERC20Upgradeable._callOptionalReturn(IERC20Upgradeable,bytes) (flattened/SupplySchedule.sol#1701-1711) is never used and should be removed
SafeERC20Upgradeable.safeApprove(IERC20Upgradeable,address,uint256) (flattened/SupplySchedule.sol#1658-1671) is never used and should be removed
SafeERC20Upgradeable.safeDecreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/SupplySchedule.sol#1682-1693) is never used and should be removed
SafeERC20Upgradeable.safeIncreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/SupplySchedule.sol#1673-1680) is never used and should be removed
SafeERC20Upgradeable.safeTransfer(IERC20Upgradeable,address,uint256) (flattened/SupplySchedule.sol#1634-1640) is never used and should be removed
SafeERC20Upgradeable.safeTransferFrom(IERC20Upgradeable,address,address,uint256) (flattened/SupplySchedule.sol#1642-1649) is never used and should be removed
SafeMathUpgradeable.add(uint256,uint256) (flattened/SupplySchedule.sol#1377-1379) is never used and should be removed
SafeMathUpgradeable.div(uint256,uint256) (flattened/SupplySchedule.sol#1419-1421) is never used and should be removed
SafeMathUpgradeable.div(uint256,uint256,string) (flattened/SupplySchedule.sol#1475-1484) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256) (flattened/SupplySchedule.sol#1435-1437) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256,string) (flattened/SupplySchedule.sol#1501-1510) is never used and should be removed
SafeMathUpgradeable.mul(uint256,uint256) (flattened/SupplySchedule.sol#1405-1407) is never used and should be removed
SafeMathUpgradeable.sub(uint256,uint256) (flattened/SupplySchedule.sol#1391-1393) is never used and should be removed
SafeMathUpgradeable.sub(uint256,uint256,string) (flattened/SupplySchedule.sol#1452-1461) is never used and should be removed
SafeMathUpgradeable.tryAdd(uint256,uint256) (flattened/SupplySchedule.sol#1306-1312) is never used and should be removed
SafeMathUpgradeable.tryDiv(uint256,uint256) (flattened/SupplySchedule.sol#1348-1353) is never used and should be removed
SafeMathUpgradeable.tryMod(uint256,uint256) (flattened/SupplySchedule.sol#1360-1365) is never used and should be removed
SafeMathUpgradeable.tryMul(uint256,uint256) (flattened/SupplySchedule.sol#1331-1341) is never used and should be removed
SafeMathUpgradeable.trySub(uint256,uint256) (flattened/SupplySchedule.sol#1319-1324) is never used and should be removed
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dead-code

Pragma version0.8.12 (flattened/SupplySchedule.sol#2) necessitates a version too recent to be trusted. Consider deploying with 0.6.12/0.7.6/0.8.7
solc-0.8.12 is not recommended for deployment
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#incorrect-versions-of-solidity

Low level call in AddressUpgradeable.sendValue(address,uint256) (flattened/SupplySchedule.sol#615-620):
	- (success) = recipient.call{value: amount}() (flattened/SupplySchedule.sol#618)
Low level call in AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/SupplySchedule.sol#683-694):
	- (success,returndata) = target.call{value: value}(data) (flattened/SupplySchedule.sol#692)
Low level call in AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/SupplySchedule.sol#712-721):
	- (success,returndata) = target.staticcall(data) (flattened/SupplySchedule.sol#719)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#low-level-calls

Event DSTestlog(string) (flattened/SupplySchedule.sol#20) is not in CapWords
Event DSTestlogs(bytes) (flattened/SupplySchedule.sol#21) is not in CapWords
Event DSTestlog_address(address) (flattened/SupplySchedule.sol#23) is not in CapWords
Event DSTestlog_bytes32(bytes32) (flattened/SupplySchedule.sol#24) is not in CapWords
Event DSTestlog_int(int256) (flattened/SupplySchedule.sol#25) is not in CapWords
Event DSTestlog_uint(uint256) (flattened/SupplySchedule.sol#26) is not in CapWords
Event DSTestlog_bytes(bytes) (flattened/SupplySchedule.sol#27) is not in CapWords
Event DSTestlog_string(string) (flattened/SupplySchedule.sol#28) is not in CapWords
Event DSTestlog_named_address(string,address) (flattened/SupplySchedule.sol#30) is not in CapWords
Event DSTestlog_named_bytes32(string,bytes32) (flattened/SupplySchedule.sol#31) is not in CapWords
Event DSTestlog_named_decimal_int(string,int256,uint256) (flattened/SupplySchedule.sol#32) is not in CapWords
Event DSTestlog_named_decimal_uint(string,uint256,uint256) (flattened/SupplySchedule.sol#33) is not in CapWords
Event DSTestlog_named_int(string,int256) (flattened/SupplySchedule.sol#34) is not in CapWords
Event DSTestlog_named_uint(string,uint256) (flattened/SupplySchedule.sol#35) is not in CapWords
Event DSTestlog_named_bytes(string,bytes) (flattened/SupplySchedule.sol#36) is not in CapWords
Event DSTestlog_named_string(string,string) (flattened/SupplySchedule.sol#37) is not in CapWords
Variable DSTest.IS_TEST (flattened/SupplySchedule.sol#39) is not in mixedCase
Modifier DSTest.logs_gas() (flattened/SupplySchedule.sol#52-57) is not in mixedCase
Function ContextUpgradeable.__Context_init() (flattened/SupplySchedule.sol#837-838) is not in mixedCase
Function ContextUpgradeable.__Context_init_unchained() (flattened/SupplySchedule.sol#840-841) is not in mixedCase
Variable ContextUpgradeable.__gap (flattened/SupplySchedule.sol#855) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init(string,string) (flattened/SupplySchedule.sol#903-905) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init_unchained(string,string) (flattened/SupplySchedule.sol#907-910) is not in mixedCase
Variable ERC20Upgradeable.__gap (flattened/SupplySchedule.sol#1242) is not in mixedCase
Function PausableUpgradeable.__Pausable_init() (flattened/SupplySchedule.sol#1545-1547) is not in mixedCase
Function PausableUpgradeable.__Pausable_init_unchained() (flattened/SupplySchedule.sol#1549-1551) is not in mixedCase
Variable PausableUpgradeable.__gap (flattened/SupplySchedule.sol#1613) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init() (flattened/SupplySchedule.sol#1751-1753) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init_unchained() (flattened/SupplySchedule.sol#1755-1757) is not in mixedCase
Variable ReentrancyGuardUpgradeable.__gap (flattened/SupplySchedule.sol#1785) is not in mixedCase
Function GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address) (flattened/SupplySchedule.sol#1961-1967) is not in mixedCase
Parameter GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address)._globalAccessControl (flattened/SupplySchedule.sol#1961) is not in mixedCase
Parameter SupplySchedule.initialize(address)._gac (flattened/SupplySchedule.sol#2051) is not in mixedCase
Parameter SupplySchedule.getEpochAtTimestamp(uint256)._timestamp (flattened/SupplySchedule.sol#2063) is not in mixedCase
Parameter SupplySchedule.getEmissionsForEpoch(uint256)._epoch (flattened/SupplySchedule.sol#2079) is not in mixedCase
Parameter SupplySchedule.setMintingStart(uint256)._globalStartTimestamp (flattened/SupplySchedule.sol#2137) is not in mixedCase
Parameter SupplySchedule.setEpochRate(uint256,uint256)._epoch (flattened/SupplySchedule.sol#2155) is not in mixedCase
Parameter SupplySchedule.setEpochRate(uint256,uint256)._rate (flattened/SupplySchedule.sol#2155) is not in mixedCase
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#conformance-to-solidity-naming-conventions

SupplySchedule._setEpochRates() (flattened/SupplySchedule.sol#2174-2181) uses literals with too many digits:
	- epochRate[0] = 593962000000000000000000 / epochLength (flattened/SupplySchedule.sol#2175)
SupplySchedule._setEpochRates() (flattened/SupplySchedule.sol#2174-2181) uses literals with too many digits:
	- epochRate[1] = 591445000000000000000000 / epochLength (flattened/SupplySchedule.sol#2176)
SupplySchedule._setEpochRates() (flattened/SupplySchedule.sol#2174-2181) uses literals with too many digits:
	- epochRate[2] = 585021000000000000000000 / epochLength (flattened/SupplySchedule.sol#2177)
SupplySchedule._setEpochRates() (flattened/SupplySchedule.sol#2174-2181) uses literals with too many digits:
	- epochRate[3] = 574138000000000000000000 / epochLength (flattened/SupplySchedule.sol#2178)
SupplySchedule._setEpochRates() (flattened/SupplySchedule.sol#2174-2181) uses literals with too many digits:
	- epochRate[4] = 558275000000000000000000 / epochLength (flattened/SupplySchedule.sol#2179)
SupplySchedule._setEpochRates() (flattened/SupplySchedule.sol#2174-2181) uses literals with too many digits:
	- epochRate[5] = 536986000000000000000000 / epochLength (flattened/SupplySchedule.sol#2180)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#too-many-digits

ERC20Upgradeable.__gap (flattened/SupplySchedule.sol#1242) is never used in ERC20Upgradeable (flattened/SupplySchedule.sol#884-1243)
ReentrancyGuardUpgradeable.__gap (flattened/SupplySchedule.sol#1785) is never used in ReentrancyGuardUpgradeable (flattened/SupplySchedule.sol#1734-1786)
PausableUpgradeable.__gap (flattened/SupplySchedule.sol#1613) is never used in SupplySchedule (flattened/SupplySchedule.sol#2029-2239)
DSTest.HEVM_ADDRESS (flattened/SupplySchedule.sol#42-43) is never used in SupplySchedule (flattened/SupplySchedule.sol#2029-2239)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-state-variable

DSTest.IS_TEST (flattened/SupplySchedule.sol#39) should be constant
SupplySchedule.epochLength (flattened/SupplySchedule.sol#2033) should be constant
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variables-that-could-be-declared-constant

name() should be declared external:
	- ERC20Upgradeable.name() (flattened/SupplySchedule.sol#915-917)
symbol() should be declared external:
	- ERC20Upgradeable.symbol() (flattened/SupplySchedule.sol#923-925)
decimals() should be declared external:
	- ERC20Upgradeable.decimals() (flattened/SupplySchedule.sol#940-942)
totalSupply() should be declared external:
	- ERC20Upgradeable.totalSupply() (flattened/SupplySchedule.sol#947-949)
balanceOf(address) should be declared external:
	- ERC20Upgradeable.balanceOf(address) (flattened/SupplySchedule.sol#954-956)
transfer(address,uint256) should be declared external:
	- ERC20Upgradeable.transfer(address,uint256) (flattened/SupplySchedule.sol#966-970)
approve(address,uint256) should be declared external:
	- ERC20Upgradeable.approve(address,uint256) (flattened/SupplySchedule.sol#989-993)
transferFrom(address,address,uint256) should be declared external:
	- ERC20Upgradeable.transferFrom(address,address,uint256) (flattened/SupplySchedule.sol#1011-1020)
increaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.increaseAllowance(address,uint256) (flattened/SupplySchedule.sol#1034-1038)
decreaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.decreaseAllowance(address,uint256) (flattened/SupplySchedule.sol#1054-1063)
initialize(address) should be declared external:
	- SupplySchedule.initialize(address) (flattened/SupplySchedule.sol#2051-2054)
getEmissionsForCurrentEpoch() should be declared external:
	- SupplySchedule.getEmissionsForCurrentEpoch() (flattened/SupplySchedule.sol#2087-2090)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#public-function-that-could-be-declared-external
flattened/SupplySchedule.sol analyzed (17 contracts with 77 detectors), 170 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
