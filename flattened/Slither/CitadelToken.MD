entreprenerd@MacBook-Pro citadel-contracts % 
entreprenerd@MacBook-Pro citadel-contracts % slither flattened/CitadelToken.sol







GlobalAccessControlManaged.gacPausable() (flattened/CitadelToken.sol#1001-1005) compares to a boolean constant:
	-require(bool,string)(paused() == false,local-paused) (flattened/CitadelToken.sol#1003)
GlobalAccessControlManaged.gacPausable() (flattened/CitadelToken.sol#1001-1005) compares to a boolean constant:
	-require(bool,string)(gac.paused() == false,global-paused) (flattened/CitadelToken.sol#1002)
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#boolean-equality