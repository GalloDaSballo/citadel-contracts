entreprenerd@MacBook-Pro citadel-contracts % slither flattened/SupplySchedule.sol     


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
Reference: https://github.com/crytic/slither/wiki/Detector-Documentation#tautology-or-contradictio