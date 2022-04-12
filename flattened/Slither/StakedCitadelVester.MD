entreprenerd@MacBook-Pro citadel-contracts % slither flattened/StakedCitadelVester.sol 



StakedCitadelVester.initialize(address,address,address)._vault (flattened/StakedCitadelVester.sol#1054) lacks a zero-check on :
		- vault = _vault (flattened/StakedCitadelVester.sol#1064)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#missing-zero-address-validation

Only the event
Reentrancy in StakedCitadelVester.claim(address,uint256) (flattened/StakedCitadelVester.sol#1076-1088):
	External calls:
	- vestingToken.safeTransfer(recipient,amount) (flattened/StakedCitadelVester.sol#1085)
	Event emitted after the call(s):
	- Claimed(msg.sender,recipient,amount) (flattened/StakedCitadelVester.sol#1086)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#reentrancy-vulnerabilities-3




GlobalAccessControlManaged.gacPausable() (flattened/StakedCitadelVester.sol#980-984) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/StakedCitadelVester.sol#981)
GlobalAccessControlManaged.gacPausable() (flattened/StakedCitadelVester.sol#980-984) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/StakedCitadelVester.sol#982)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality
