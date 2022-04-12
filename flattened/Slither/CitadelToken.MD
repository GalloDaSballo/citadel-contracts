entreprenerd@MacBook-Pro citadel-contracts % 
entreprenerd@MacBook-Pro citadel-contracts % slither flattened/CitadelToken.sol

ERC20Upgradeable.__gap (flattened/CitadelToken.sol#808) shadows:
	- ContextUpgradeable.__gap (flattened/CitadelToken.sol#421)
PausableUpgradeable.__gap (flattened/CitadelToken.sol#911) shadows:
	- ContextUpgradeable.__gap (flattened/CitadelToken.sol#421)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variable-shadowing

CitadelToken.initialize(string,string,address)._name (flattened/CitadelToken.sol#1037) shadows:
	- ERC20Upgradeable._name (flattened/CitadelToken.sol#457) (state variable)
CitadelToken.initialize(string,string,address)._symbol (flattened/CitadelToken.sol#1038) shadows:
	- ERC20Upgradeable._symbol (flattened/CitadelToken.sol#458) (state variable)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#local-variable-shadowing

AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/CitadelToken.sol#295-315) uses assembly
	- INLINE ASM (flattened/CitadelToken.sol#307-310)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#assembly-usage

GlobalAccessControlManaged.gacPausable() (flattened/CitadelToken.sol#1001-1005) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/CitadelToken.sol#1003)
GlobalAccessControlManaged.gacPausable() (flattened/CitadelToken.sol#1001-1005) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/CitadelToken.sol#1002)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality

AddressUpgradeable.functionCall(address,bytes) (flattened/CitadelToken.sol#206-208) is never used and should be removed
AddressUpgradeable.functionCall(address,bytes,string) (flattened/CitadelToken.sol#216-222) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256) (flattened/CitadelToken.sol#235-241) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/CitadelToken.sol#249-260) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes) (flattened/CitadelToken.sol#268-270) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/CitadelToken.sol#278-287) is never used and should be removed
AddressUpgradeable.sendValue(address,uint256) (flattened/CitadelToken.sol#181-186) is never used and should be removed
AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/CitadelToken.sol#295-315) is never used and should be removed
ContextUpgradeable.__Context_init() (flattened/CitadelToken.sol#403-404) is never used and should be removed
ContextUpgradeable.__Context_init_unchained() (flattened/CitadelToken.sol#406-407) is never used and should be removed
ContextUpgradeable._msgData() (flattened/CitadelToken.sol#412-414) is never used and should be removed
ERC20Upgradeable._burn(address,uint256) (flattened/CitadelToken.sol#699-714) is never used and should be removed
PausableUpgradeable.__Pausable_init() (flattened/CitadelToken.sol#843-845) is never used and should be removed
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dead-code

Pragma version^0.8.0 (flattened/CitadelToken.sol#2) allows old versions
solc-0.8.12 is not recommended for deployment
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#incorrect-versions-of-solidity

Low level call in AddressUpgradeable.sendValue(address,uint256) (flattened/CitadelToken.sol#181-186):
	- (success) = recipient.call{value: amount}() (flattened/CitadelToken.sol#184)
Low level call in AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/CitadelToken.sol#249-260):
	- (success,returndata) = target.call{value: value}(data) (flattened/CitadelToken.sol#258)
Low level call in AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/CitadelToken.sol#278-287):
	- (success,returndata) = target.staticcall(data) (flattened/CitadelToken.sol#285)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#low-level-calls

Function ContextUpgradeable.__Context_init() (flattened/CitadelToken.sol#403-404) is not in mixedCase
Function ContextUpgradeable.__Context_init_unchained() (flattened/CitadelToken.sol#406-407) is not in mixedCase
Variable ContextUpgradeable.__gap (flattened/CitadelToken.sol#421) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init(string,string) (flattened/CitadelToken.sol#469-471) is not in mixedCase
Function ERC20Upgradeable.__ERC20_init_unchained(string,string) (flattened/CitadelToken.sol#473-476) is not in mixedCase
Variable ERC20Upgradeable.__gap (flattened/CitadelToken.sol#808) is not in mixedCase
Function PausableUpgradeable.__Pausable_init() (flattened/CitadelToken.sol#843-845) is not in mixedCase
Function PausableUpgradeable.__Pausable_init_unchained() (flattened/CitadelToken.sol#847-849) is not in mixedCase
Variable PausableUpgradeable.__gap (flattened/CitadelToken.sol#911) is not in mixedCase
Function GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address) (flattened/CitadelToken.sol#958-964) is not in mixedCase
Parameter GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address)._globalAccessControl (flattened/CitadelToken.sol#958) is not in mixedCase
Parameter CitadelToken.initialize(string,string,address)._name (flattened/CitadelToken.sol#1037) is not in mixedCase
Parameter CitadelToken.initialize(string,string,address)._symbol (flattened/CitadelToken.sol#1038) is not in mixedCase
Parameter CitadelToken.initialize(string,string,address)._gac (flattened/CitadelToken.sol#1039) is not in mixedCase
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#conformance-to-solidity-naming-conventions

ERC20Upgradeable.__gap (flattened/CitadelToken.sol#808) is never used in CitadelToken (flattened/CitadelToken.sol#1022-1061)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-state-variable

name() should be declared external:
	- ERC20Upgradeable.name() (flattened/CitadelToken.sol#481-483)
symbol() should be declared external:
	- ERC20Upgradeable.symbol() (flattened/CitadelToken.sol#489-491)
decimals() should be declared external:
	- ERC20Upgradeable.decimals() (flattened/CitadelToken.sol#506-508)
totalSupply() should be declared external:
	- ERC20Upgradeable.totalSupply() (flattened/CitadelToken.sol#513-515)
balanceOf(address) should be declared external:
	- ERC20Upgradeable.balanceOf(address) (flattened/CitadelToken.sol#520-522)
transfer(address,uint256) should be declared external:
	- ERC20Upgradeable.transfer(address,uint256) (flattened/CitadelToken.sol#532-536)
approve(address,uint256) should be declared external:
	- ERC20Upgradeable.approve(address,uint256) (flattened/CitadelToken.sol#555-559)
transferFrom(address,address,uint256) should be declared external:
	- ERC20Upgradeable.transferFrom(address,address,uint256) (flattened/CitadelToken.sol#577-586)
increaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.increaseAllowance(address,uint256) (flattened/CitadelToken.sol#600-604)
decreaseAllowance(address,uint256) should be declared external:
	- ERC20Upgradeable.decreaseAllowance(address,uint256) (flattened/CitadelToken.sol#620-629)
initialize(string,string,address) should be declared external:
	- CitadelToken.initialize(string,string,address) (flattened/CitadelToken.sol#1036-1043)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#public-function-that-could-be-declared-external
flattened/CitadelToken.sol analyzed (10 contracts with 77 detectors), 51 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
