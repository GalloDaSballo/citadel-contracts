entreprenerd@MacBook-Pro citadel-contracts % slither flattened/StakedCitadelVester.sol 

PausableUpgradeable.__gap (flattened/StakedCitadelVester.sol#890) shadows:
	- ContextUpgradeable.__gap (flattened/StakedCitadelVester.sol#793)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#state-variable-shadowing

StakedCitadelVester.initialize(address,address,address)._vault (flattened/StakedCitadelVester.sol#1054) lacks a zero-check on :
		- vault = _vault (flattened/StakedCitadelVester.sol#1064)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#missing-zero-address-validation

Reentrancy in StakedCitadelVester.claim(address,uint256) (flattened/StakedCitadelVester.sol#1076-1088):
	External calls:
	- vestingToken.safeTransfer(recipient,amount) (flattened/StakedCitadelVester.sol#1085)
	Event emitted after the call(s):
	- Claimed(msg.sender,recipient,amount) (flattened/StakedCitadelVester.sol#1086)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-3

StakedCitadelVester.claim(address,uint256) (flattened/StakedCitadelVester.sol#1076-1088) uses timestamp for comparisons
	Dangerous comparisons:
	- amount > claimable (flattened/StakedCitadelVester.sol#1078)
	- amount != 0 (flattened/StakedCitadelVester.sol#1081)
StakedCitadelVester.claimableBalance(address) (flattened/StakedCitadelVester.sol#1099-1113) uses timestamp for comparisons
	Dangerous comparisons:
	- block.timestamp >= vesting[recipient].unlockEnd (flattened/StakedCitadelVester.sol#1102)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#block-timestamp

AddressUpgradeable.verifyCallResult(bool,bytes,string) (flattened/StakedCitadelVester.sol#488-508) uses assembly
	- INLINE ASM (flattened/StakedCitadelVester.sol#500-503)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#assembly-usage

GlobalAccessControlManaged.gacPausable() (flattened/StakedCitadelVester.sol#980-984) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/StakedCitadelVester.sol#981)
GlobalAccessControlManaged.gacPausable() (flattened/StakedCitadelVester.sol#980-984) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/StakedCitadelVester.sol#982)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality

AddressUpgradeable.functionCall(address,bytes) (flattened/StakedCitadelVester.sol#399-401) is never used and should be removed
AddressUpgradeable.functionCallWithValue(address,bytes,uint256) (flattened/StakedCitadelVester.sol#428-434) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes) (flattened/StakedCitadelVester.sol#461-463) is never used and should be removed
AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/StakedCitadelVester.sol#471-480) is never used and should be removed
AddressUpgradeable.sendValue(address,uint256) (flattened/StakedCitadelVester.sol#374-379) is never used and should be removed
ContextUpgradeable.__Context_init() (flattened/StakedCitadelVester.sol#775-776) is never used and should be removed
ContextUpgradeable.__Context_init_unchained() (flattened/StakedCitadelVester.sol#778-779) is never used and should be removed
ContextUpgradeable._msgData() (flattened/StakedCitadelVester.sol#784-786) is never used and should be removed
PausableUpgradeable.__Pausable_init() (flattened/StakedCitadelVester.sol#822-824) is never used and should be removed
SafeERC20Upgradeable.safeApprove(IERC20Upgradeable,address,uint256) (flattened/StakedCitadelVester.sol#547-560) is never used and should be removed
SafeERC20Upgradeable.safeDecreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/StakedCitadelVester.sol#571-582) is never used and should be removed
SafeERC20Upgradeable.safeIncreaseAllowance(IERC20Upgradeable,address,uint256) (flattened/StakedCitadelVester.sol#562-569) is never used and should be removed
SafeERC20Upgradeable.safeTransferFrom(IERC20Upgradeable,address,address,uint256) (flattened/StakedCitadelVester.sol#531-538) is never used and should be removed
SafeMathUpgradeable.div(uint256,uint256,string) (flattened/StakedCitadelVester.sol#274-283) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256) (flattened/StakedCitadelVester.sol#234-236) is never used and should be removed
SafeMathUpgradeable.mod(uint256,uint256,string) (flattened/StakedCitadelVester.sol#300-309) is never used and should be removed
SafeMathUpgradeable.sub(uint256,uint256,string) (flattened/StakedCitadelVester.sol#251-260) is never used and should be removed
SafeMathUpgradeable.tryAdd(uint256,uint256) (flattened/StakedCitadelVester.sol#105-111) is never used and should be removed
SafeMathUpgradeable.tryDiv(uint256,uint256) (flattened/StakedCitadelVester.sol#147-152) is never used and should be removed
SafeMathUpgradeable.tryMod(uint256,uint256) (flattened/StakedCitadelVester.sol#159-164) is never used and should be removed
SafeMathUpgradeable.tryMul(uint256,uint256) (flattened/StakedCitadelVester.sol#130-140) is never used and should be removed
SafeMathUpgradeable.trySub(uint256,uint256) (flattened/StakedCitadelVester.sol#118-123) is never used and should be removed
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#dead-code

Pragma version0.8.12 (flattened/StakedCitadelVester.sol#2) necessitates a version too recent to be trusted. Consider deploying with 0.6.12/0.7.6/0.8.7
solc-0.8.12 is not recommended for deployment
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#incorrect-versions-of-solidity

Low level call in AddressUpgradeable.sendValue(address,uint256) (flattened/StakedCitadelVester.sol#374-379):
	- (success) = recipient.call{value: amount}() (flattened/StakedCitadelVester.sol#377)
Low level call in AddressUpgradeable.functionCallWithValue(address,bytes,uint256,string) (flattened/StakedCitadelVester.sol#442-453):
	- (success,returndata) = target.call{value: value}(data) (flattened/StakedCitadelVester.sol#451)
Low level call in AddressUpgradeable.functionStaticCall(address,bytes,string) (flattened/StakedCitadelVester.sol#471-480):
	- (success,returndata) = target.staticcall(data) (flattened/StakedCitadelVester.sol#478)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#low-level-calls

Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init() (flattened/StakedCitadelVester.sol#718-720) is not in mixedCase
Function ReentrancyGuardUpgradeable.__ReentrancyGuard_init_unchained() (flattened/StakedCitadelVester.sol#722-724) is not in mixedCase
Variable ReentrancyGuardUpgradeable.__gap (flattened/StakedCitadelVester.sol#752) is not in mixedCase
Function ContextUpgradeable.__Context_init() (flattened/StakedCitadelVester.sol#775-776) is not in mixedCase
Function ContextUpgradeable.__Context_init_unchained() (flattened/StakedCitadelVester.sol#778-779) is not in mixedCase
Variable ContextUpgradeable.__gap (flattened/StakedCitadelVester.sol#793) is not in mixedCase
Function PausableUpgradeable.__Pausable_init() (flattened/StakedCitadelVester.sol#822-824) is not in mixedCase
Function PausableUpgradeable.__Pausable_init_unchained() (flattened/StakedCitadelVester.sol#826-828) is not in mixedCase
Variable PausableUpgradeable.__gap (flattened/StakedCitadelVester.sol#890) is not in mixedCase
Function GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address) (flattened/StakedCitadelVester.sol#937-943) is not in mixedCase
Parameter GlobalAccessControlManaged.__GlobalAccessControlManaged_init(address)._globalAccessControl (flattened/StakedCitadelVester.sol#937) is not in mixedCase
Parameter StakedCitadelVester.initialize(address,address,address)._gac (flattened/StakedCitadelVester.sol#1052) is not in mixedCase
Parameter StakedCitadelVester.initialize(address,address,address)._vestingToken (flattened/StakedCitadelVester.sol#1053) is not in mixedCase
Parameter StakedCitadelVester.initialize(address,address,address)._vault (flattened/StakedCitadelVester.sol#1054) is not in mixedCase
Parameter StakedCitadelVester.vest(address,uint256,uint256)._amount (flattened/StakedCitadelVester.sol#1129) is not in mixedCase
Parameter StakedCitadelVester.vest(address,uint256,uint256)._unlockBegin (flattened/StakedCitadelVester.sol#1130) is not in mixedCase
Parameter StakedCitadelVester.setVestingDuration(uint256)._duration (flattened/StakedCitadelVester.sol#1158) is not in mixedCase
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#conformance-to-solidity-naming-conventions

ReentrancyGuardUpgradeable.__gap (flattened/StakedCitadelVester.sol#752) is never used in StakedCitadelVester (flattened/StakedCitadelVester.sol#1005-1165)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#unused-state-variable
flattened/StakedCitadelVester.sol analyzed (11 contracts with 77 detectors), 53 result(s) found
entreprenerd@MacBook-Pro citadel-contracts % 
