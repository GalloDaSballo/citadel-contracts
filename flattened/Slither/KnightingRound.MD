entreprenerd@MacBook-Pro citadel-contracts % 
entreprenerd@MacBook-Pro citadel-contracts % slither flattened/KnightingRound.sol 

ERC20Upgradeable.__gap (flattened/KnightingRound.sol#808) shadows:
	- ContextUpgradeable.__gap (flattened/KnightingRound.sol#421)
PausableUpgradeable.__gap (flattened/KnightingRound.sol#1244) shadows:
	- ContextUpgradeable.__gap (flattened/KnightingRound.sol#421)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variable-shadowing

Reentrancy in KnightingRound.buy(uint256,uint8,bytes32[]) (flattened/KnightingRound.sol#1507-1549):
	External calls:
	- tokenIn.safeTransferFrom(msg.sender,saleRecipient,_tokenInAmount) (flattened/KnightingRound.sol#1546)
	Event emitted after the call(s):
	- Sale(msg.sender,_daoId,_tokenInAmount,tokenOutAmount_) (flattened/KnightingRound.sol#1548)
Reentrancy in KnightingRound.claim() (flattened/KnightingRound.sol#1554-1568):
	External calls:
	- tokenOut.safeTransfer(msg.sender,tokenOutAmount_) (flattened/KnightingRound.sol#1565)
	Event emitted after the call(s):
	- Claim(msg.sender,tokenOutAmount_) (flattened/KnightingRound.sol#1567)
Reentrancy in KnightingRound.sweep(address) (flattened/KnightingRound.sol#1747-1762):
	External calls:
	- ERC20Upgradeable(_token).safeTransfer(saleRecipient,amount) (flattened/KnightingRound.sol#1759)
	Event emitted after the call(s):
	- Sweep(_token,amount) (flattened/KnightingRound.sol#1761)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-3

KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256) (flattened/KnightingRound.sol#1454-1494) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(_saleStart >= block.timestamp,KnightingRound: start date may not be in the past) (flattened/KnightingRound.sol#1465-1468)
KnightingRound.buy(uint256,uint8,bytes32[]) (flattened/KnightingRound.sol#1507-1549) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(saleStart <= block.timestamp,KnightingRound: not started) (flattened/KnightingRound.sol#1512)
	- require(bool,string)(block.timestamp < saleStart + saleDuration,KnightingRound: already ended) (flattened/KnightingRound.sol#1513-1516)
KnightingRound.saleEnded() (flattened/KnightingRound.sol#1603-1607) uses timestamp for comparisons
	Dangerous comparisons:
	- hasEnded_ = (block.timestamp >= saleStart + saleDuration) || (totalTokenIn >= tokenInLimit) (flattened/KnightingRound.sol#1604-1606)
KnightingRound.setSaleStart(uint256) (flattened/KnightingRound.sol#1634-1647) uses timestamp for comparisons
	Dangerous comparisons:
	- require(bool,string)(_saleStart >= block.timestamp,KnightingRound: start date may not be in the past) (flattened/KnightingRound.sol#1638-1641)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#block-timestamp

AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/KnightingRound.sol#295-315) uses assembly
	- INLINE ASM (flattened/KnightingRound.sol#307-310)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#assembly-usage

GlobalAccessControlManaged.gacPausable() (flattened/KnightingRound.sol#1334-1338) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/KnightingRound.sol#1335)
GlobalAccessControlManaged.gacPausable() (flattened/KnightingRound.sol#1334-1338) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/KnightingRound.sol#1336)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality

AddressUpgradeable.functionCall(address,bytes) (flattened/KnightingRound.sol#206-208) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256) (flattened/KnightingRound.sol#235-241) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes) (flattened/KnightingRound.sol#268-270) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/KnightingRound.sol#278-287) is never used and should be removed
AddressUpgradeable.sendValue(address,uint256) (flattened/KnightingRound.sol#181-186) is never used and should be removed
ContextUpgradeable.__Context_init() (flattened/KnightingRound.sol#403-404) is never used and should be removed
ContextUpgradeable.__Context_init_unchained() (flattened/KnightingRound.sol#406-407) is never used and should be removed
ContextUpgradeable._msgData() (flattened/KnightingRound.sol#412-414) is never used and should be removed
ERC20Upgradeable.__ERC20_init(string,string) (flattened/KnightingRound.sol#469-471) is never used and should be removed
ERC20Upgradeable.__ERC20_init_unchained(string,string) (flattened/KnightingRound.sol#473-476) is never used and should be removed
ERC20Upgradeable._burn(address,uint256) (flattened/KnightingRound.sol#699-714) is never used and should be removed
ERC20Upgradeable._mint(address,uint256) (flattened/KnightingRound.sol#676-686) is never used and should be removed
PausableUpgradeable.__Pausable_init() (flattened/KnightingRound.sol#1176-1178) is never used and should be removed
SafeERC20Upgradeable.safeApprove(IERC20Upgradeable,address,uint256) (flattened/KnightingRound.sol#853-866) is never used and should be removed
SafeERC20Upgradeable.safeDecreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/KnightingRound.sol#877-888) is never used and should be removed
SafeERC20Upgradeable.safeIncreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/KnightingRound.sol#868-875) is never used and should be removed
SafeMathUpgradeable.div(uint256,uint256) (flattened/KnightingRound.sol#1041-1043) is never used and should be removed
SafeMathUpgradeable.div(uint256,uint256,string) (flattened/KnightingRound.sol#1097-1106) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256) (flattened/KnightingRound.sol#1057-1059) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256,string) (flattened/KnightingRound.sol#1123-1132) is never used and should be removed
SafeMathUpgradeable.mul(uint256,uint256) (flattened/KnightingRound.sol#1027-1029) is never used and should be removed
SafeMathUpgradeable.sub(uint256,uint256,string) (flattened/KnightingRound.sol#1074-1083) is never used and should be removed
SafeMathUpgradeable.tryAdd(uint256,uint256) (flattened/KnightingRound.sol#928-934) is never used and should be removed
SafeMathUpgradeable.tryDiv(uint256,uint256) (flattened/KnightingRound.sol#970-975) is never used and should be removed
SafeMathUpgradeable.tryMod(uint256,uint256) (flattened/KnightingRound.sol#982-987) is never used and should be removed
SafeMathUpgradeable.tryMul(uint256,uint256) (flattened/KnightingRound.sol#953-963) is never used and should be removed
SafeMathUpgradeable.trySub(uint256,uint256) (flattened/KnightingRound.sol#941-946) is never used and should be removed
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dead-code

Pragma version0.8.12 (flattened/KnightingRound.sol#2) necessitates a version too recent to be trusted. Consider deploying with 0.6.12/0.7.6/0.8.7
solc-0.8.12 is not recommended for deployment
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#incorrect-versions-of-solidity

Low level call in AddressUpgradeable.sendValue(address,uint256) (flattened/KnightingRound.sol#181-186):
	- (success) = recipient.call{value: amount}() (flattened/KnightingRound.sol#184)
Low level call in AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/KnightingRound.sol#249-260):
	- (success,returndata) = target.call{value: value}(data) (flattened/KnightingRound.sol#258)
Low level call in AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/KnightingRound.sol#278-287):
	- (success,returndata) = target.staticcall(data) (flattened/KnightingRound.sol#285)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#low-level-calls

Function ContextUpgradeable.__Context_init() (flattened/KnightingRound.sol#403-404) is not in mixedCase
Function ContextUpgradeable.__Context_init_unchained() (flattened/KnightingRound.sol#406-407) is not in mixedCase
Variable ContextUpgradeable.__gap (flattened/KnightingRound.sol#421) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init(string,string) (flattened/KnightingRound.sol#469-471) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init_unchained(string,string) (flattened/KnightingRound.sol#473-476) is not in mixedCase
Variable ERC20Upgradeable.__gap (flattened/KnightingRound.sol#808) is not in mixedCase
Function PausableUpgradeable.__Pausable_init() (flattened/KnightingRound.sol#1176-1178) is not in mixedCase
Function PausableUpgradeable.__Pausable_init_unchained() (flattened/KnightingRound.sol#1180-1182) is not in mixedCase
Variable PausableUpgradeable.__gap (flattened/KnightingRound.sol#1244) is not in mixedCase
Function GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address) (flattened/KnightingRound.sol#1291-1297) is not in mixedCase
Parameter GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address)._globalAccessControl (flattened/KnightingRound.sol#1291) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._globalAccessControl (flattened/KnightingRound.sol#1455) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._tokenOut (flattened/KnightingRound.sol#1456) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._tokenIn (flattened/KnightingRound.sol#1457) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._saleStart (flattened/KnightingRound.sol#1458) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._saleDuration (flattened/KnightingRound.sol#1459) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._tokenOutPrice (flattened/KnightingRound.sol#1460) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._saleRecipient (flattened/KnightingRound.sol#1461) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._guestlist (flattened/KnightingRound.sol#1462) is not in mixedCase
Parameter KnightingRound.initialize(address,address,address,uint256,uint256,uint256,address,address,uint256)._tokenInLimit (flattened/KnightingRound.sol#1463) is not in mixedCase
Parameter KnightingRound.buy(uint256,uint8,bytes32[])._tokenInAmount (flattened/KnightingRound.sol#1508) is not in mixedCase
Parameter KnightingRound.buy(uint256,uint8,bytes32[])._daoId (flattened/KnightingRound.sol#1509) is not in mixedCase
Parameter KnightingRound.buy(uint256,uint8,bytes32[])._proof (flattened/KnightingRound.sol#1510) is not in mixedCase
Parameter KnightingRound.getAmountOut(uint256)._tokenInAmount (flattened/KnightingRound.sol#1579) is not in mixedCase
Parameter KnightingRound.setSaleStart(uint256)._saleStart (flattened/KnightingRound.sol#1634) is not in mixedCase
Parameter KnightingRound.setSaleDuration(uint256)._saleDuration (flattened/KnightingRound.sol#1653) is not in mixedCase
Parameter KnightingRound.setTokenOutPrice(uint256)._tokenOutPrice (flattened/KnightingRound.sol#1672) is not in mixedCase
Parameter KnightingRound.setSaleRecipient(address)._saleRecipient (flattened/KnightingRound.sol#1690) is not in mixedCase
Parameter KnightingRound.setGuestlist(address)._guestlist (flattened/KnightingRound.sol#1712) is not in mixedCase
Parameter KnightingRound.setTokenInLimit(uint256)._tokenInLimit (flattened/KnightingRound.sol#1725) is not in mixedCase
Parameter KnightingRound.sweep(address)._token (flattened/KnightingRound.sol#1747) is not in mixedCase
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#conformance-to-solidity-naming-conventions

ERC20Upgradeable.__gap (flattened/KnightingRound.sol#808) is never used in ERC20Upgradeable (flattened/KnightingRound.sol#450-809)
PausableUpgradeable.__gap (flattened/KnightingRound.sol#1244) is never used in KnightingRound (flattened/KnightingRound.sol#1360-1764)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-state-variable

name() should be declared external:
	- ERC20Upgradeable.name() (flattened/KnightingRound.sol#481-483)
symbol() should be declared external:
	- ERC20Upgradeable.symbol() (flattened/KnightingRound.sol#489-491)
decimals() should be declared external:
	- ERC20Upgradeable.decimals() (flattened/KnightingRound.sol#506-508)
totalSupply() should be declared external:
	- ERC20Upgradeable.totalSupply() (flattened/KnightingRound.sol#513-515)
balanceOf(address) should be declared external:
	- ERC20Upgradeable.balanceOf(address) (flattened/KnightingRound.sol#520-522)
transfer(address,uint256) should be declared external:
	- ERC20Upgradeable.transfer(address,uint256) (flattened/KnightingRound.sol#532-536)
approve(address,uint256) should be declared external:
	- ERC20Upgradeable.approve(address,uint256) (flattened/KnightingRound.sol#555-559)
transferFrom(address,address,uint256) should be declared external:
	- ERC20Upgradeable.transferFrom(address,address,uint256) (flattened/KnightingRound.sol#577-586)
increaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.increaseAllowance(address,uint256) (flattened/KnightingRound.sol#600-604)
decreaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.decreaseAllowance(address,uint256) (flattened/KnightingRound.sol#620-629)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#public-function-that-could-be-declared-external
flattened/KnightingRound.sol analyzed (13 contracts with 77 detectors), 87 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
