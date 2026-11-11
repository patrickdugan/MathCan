// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

// This file is copied into test/ of Uniswap/v4-core at the pinned commit.
// It exercises the actual PoolManager and Pool.swap rather than reimplementing
// concentrated liquidity in a Python test double.
import {Deployers} from "./utils/Deployers.sol";
import {Vm} from "forge-std/Vm.sol";
import {MockERC20} from "solmate/src/test/utils/mocks/MockERC20.sol";
import {IPoolManager} from "../src/interfaces/IPoolManager.sol";
import {IUnlockCallback} from "../src/interfaces/callback/IUnlockCallback.sol";
import {IHooks} from "../src/interfaces/IHooks.sol";
import {Hooks} from "../src/libraries/Hooks.sol";
import {StateLibrary} from "../src/libraries/StateLibrary.sol";
import {TransientStateLibrary} from "../src/libraries/TransientStateLibrary.sol";
import {Currency, CurrencyLibrary} from "../src/types/Currency.sol";
import {PoolKey} from "../src/types/PoolKey.sol";
import {PoolId, PoolIdLibrary} from "../src/types/PoolId.sol";
import {SwapParams} from "../src/types/PoolOperation.sol";
import {BalanceDelta} from "../src/types/BalanceDelta.sol";
import {MockHooks} from "../src/test/MockHooks.sol";
import {CurrencySettler} from "./utils/CurrencySettler.sol";

contract MathCanObservedRouter is IUnlockCallback {
    using CurrencySettler for Currency;
    using StateLibrary for IPoolManager;
    using TransientStateLibrary for IPoolManager;
    using PoolIdLibrary for PoolKey;
    using CurrencyLibrary for Currency;

    IPoolManager public immutable manager;
    string public constant MARKER = "CHTR08-real-swap";

    struct Observation {
        int256 delta0;
        int256 delta1;
        int256 delta0Before;
        int256 delta1Before;
        int256 delta0Settled;
        int256 delta1Settled;
        uint256 nonzeroBeforeSwap;
        uint256 nonzeroAtSwap;
        uint256 nonzeroAfterSettlement;
        bool unlockedAtSwap;
        uint160 priceAfter;
        int24 tickAfter;
        uint128 liquidityAfter;
    }

    constructor(IPoolManager manager_) { manager = manager_; }

    function execute(PoolKey memory key, SwapParams memory params)
        external returns (Observation memory obs)
    {
        bytes memory raw = manager.unlock(abi.encode(key, params, msg.sender));
        obs = abi.decode(raw, (Observation));
    }

    function unlockCallback(bytes calldata raw) external returns (bytes memory) {
        require(msg.sender == address(manager), "only manager may call callback");
        (PoolKey memory key, SwapParams memory params, address payer) =
            abi.decode(raw, (PoolKey, SwapParams, address));

        Observation memory obs;
        obs.delta0Before = manager.currencyDelta(address(this), key.currency0);
        obs.delta1Before = manager.currencyDelta(address(this), key.currency1);
        obs.nonzeroBeforeSwap = manager.getNonzeroDeltaCount();
        require(obs.delta0Before == 0 && obs.delta1Before == 0 && obs.nonzeroBeforeSwap == 0,
                "nonzero initial transient deltas");
        BalanceDelta execution = manager.swap(key, params, bytes(MARKER));
        obs.delta0 = manager.currencyDelta(address(this), key.currency0);
        obs.delta1 = manager.currencyDelta(address(this), key.currency1);
        obs.nonzeroAtSwap = manager.getNonzeroDeltaCount();
        obs.unlockedAtSwap = manager.isUnlocked();
        (obs.priceAfter, obs.tickAfter,,) = manager.getSlot0(key.toId());
        obs.liquidityAfter = manager.getLiquidity(key.toId());

        require(obs.unlockedAtSwap, "unlock flag absent");
        require(obs.delta0 == execution.amount0(), "currency0 mismatch");
        require(obs.delta1 == execution.amount1(), "currency1 mismatch");
        require(obs.nonzeroAtSwap == 2, "expected two nonzero swap deltas");

        if (obs.delta0 < 0) key.currency0.settle(manager, payer, uint256(-obs.delta0), false);
        if (obs.delta1 < 0) key.currency1.settle(manager, payer, uint256(-obs.delta1), false);
        if (obs.delta0 > 0) key.currency0.take(manager, payer, uint256(obs.delta0), false);
        if (obs.delta1 > 0) key.currency1.take(manager, payer, uint256(obs.delta1), false);
        obs.nonzeroAfterSettlement = manager.getNonzeroDeltaCount();
        obs.delta0Settled = manager.currencyDelta(address(this), key.currency0);
        obs.delta1Settled = manager.currencyDelta(address(this), key.currency1);
        require(obs.nonzeroAfterSettlement == 0 && obs.delta0Settled == 0 && obs.delta1Settled == 0,
                "unsettled deltas");
        return abi.encode(obs);
    }
}

contract MathCanCHTR08 is Deployers {
    using StateLibrary for IPoolManager;
    using TransientStateLibrary for IPoolManager;
    using PoolIdLibrary for PoolKey;
    using CurrencyLibrary for Currency;

    string internal constant CORE_COMMIT = "bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6";
    MathCanObservedRouter internal probe;
    MockHooks internal hook;

    function setUp() public {
        deployFreshManagerAndRouters();
        deployMintAndApprove2Currencies();

        // PoolManager validates permission bits in the address. Etching copies
        // the MockHooks runtime code onto an address with exactly both swap bits.
        address hookAddress = address(uint160(Hooks.BEFORE_SWAP_FLAG | Hooks.AFTER_SWAP_FLAG));
        MockHooks implementation = new MockHooks();
        vm.etch(hookAddress, address(implementation).code);
        hook = MockHooks(hookAddress);
        (key,) = initPoolAndAddLiquidity(currency0, currency1, IHooks(hookAddress), 3000, SQRT_PRICE_1_1);

        probe = new MathCanObservedRouter(manager);
        MockERC20(Currency.unwrap(currency0)).approve(address(probe), type(uint256).max);
        MockERC20(Currency.unwrap(currency1)).approve(address(probe), type(uint256).max);
    }

    function test_chtr08_actual_pool_swap_and_hook() public {
        PoolId id = key.toId();
        (uint160 priceBefore, int24 tickBefore,,) = manager.getSlot0(id);
        uint128 liquidityBefore = manager.getLiquidity(id);
        uint256 trader0Before = currency0.balanceOf(address(this));
        uint256 trader1Before = currency1.balanceOf(address(this));
        uint256 vault0Before = currency0.balanceOf(address(manager));
        uint256 vault1Before = currency1.balanceOf(address(manager));

        SwapParams memory params = SwapParams({
            zeroForOne: true,
            amountSpecified: -int256(1e12),
            sqrtPriceLimitX96: MIN_PRICE_LIMIT
        });
        vm.recordLogs();
        MathCanObservedRouter.Observation memory obs = probe.execute(key, params);
        Vm.Log[] memory logs = vm.getRecordedLogs();
        bool seenSwap;
        bytes32 swapSignature = keccak256("Swap(bytes32,address,int128,int128,uint160,uint128,int24,uint24)");
        int128 event0;
        int128 event1;
        uint160 eventPrice;
        int24 eventTick;
        uint128 eventLiquidity;
        uint24 eventFee;
        for (uint256 i = 0; i < logs.length; ++i) {
            if (logs[i].emitter != address(manager) || logs[i].topics.length < 3
                    || logs[i].topics[0] != swapSignature) continue;
            require(!seenSwap, "duplicate Swap event");
            seenSwap = true;
            require(logs[i].topics[1] == PoolId.unwrap(id), "wrong pool id");
            require(address(uint160(uint256(logs[i].topics[2]))) == address(probe), "wrong swap sender");
            (event0, event1, eventPrice, eventLiquidity, eventTick, eventFee) =
                abi.decode(logs[i].data, (int128, int128, uint160, uint128, int24, uint24));
        }
        require(seenSwap, "PoolManager Swap log missing");
        require(event0 == obs.delta0 && event1 == obs.delta1, "event/delta mismatch");
        require(eventPrice == obs.priceAfter && eventTick == obs.tickAfter, "event/slot0 mismatch");
        require(eventLiquidity == obs.liquidityAfter, "event/liquidity mismatch");
        require(obs.priceAfter < priceBefore && obs.tickAfter <= tickBefore, "price did not decrease");
        require(obs.liquidityAfter == liquidityBefore && liquidityBefore > 0, "liquidity changed");
        require(obs.nonzeroAtSwap == 2 && obs.nonzeroAfterSettlement == 0, "wrong delta count");
        require(!manager.isUnlocked() && manager.getNonzeroDeltaCount() == 0, "unlock did not close");
        require(keccak256(hook.beforeSwapData()) == keccak256(bytes(probe.MARKER())), "beforeSwap omitted");
        require(keccak256(hook.afterSwapData()) == keccak256(bytes(probe.MARKER())), "afterSwap omitted");

        uint256 trader0After = currency0.balanceOf(address(this));
        uint256 trader1After = currency1.balanceOf(address(this));
        uint256 vault0After = currency0.balanceOf(address(manager));
        uint256 vault1After = currency1.balanceOf(address(manager));
        require(obs.delta0 < 0 && obs.delta1 > 0, "unexpected exact-input signs");
        require(int256(trader0After) - int256(trader0Before) == obs.delta0, "trader0 conservation");
        require(int256(trader1After) - int256(trader1Before) == obs.delta1, "trader1 conservation");
        require(int256(vault0After) - int256(vault0Before) == -obs.delta0, "vault0 conservation");
        require(int256(vault1After) - int256(vault1Before) == -obs.delta1, "vault1 conservation");

        // File is a Foundry-generated observation in CI, not a raw opcode trace.
        string memory k = "mathcan_chtr08";
        vm.serializeString(k, "schema", "mathcan.chtr08.foundry-observation.v1");
        vm.serializeString(k, "source_commit", CORE_COMMIT);
        vm.serializeAddress(k, "manager", address(manager));
        vm.serializeAddress(k, "probe_router", address(probe));
        vm.serializeAddress(k, "hook", address(hook));
        vm.serializeAddress(k, "currency0", Currency.unwrap(currency0));
        vm.serializeAddress(k, "currency1", Currency.unwrap(currency1));
        vm.serializeBytes32(k, "pool_id", PoolId.unwrap(id));
        vm.serializeBytes32(k, "manager_runtime_hash", address(manager).codehash);
        vm.serializeBytes32(k, "hook_runtime_hash", address(hook).codehash);
        vm.serializeInt(k, "swap_amount_specified", params.amountSpecified);
        vm.serializeInt(k, "caller_delta0_before", obs.delta0Before);
        vm.serializeInt(k, "caller_delta1_before", obs.delta1Before);
        vm.serializeInt(k, "caller_delta0", obs.delta0);
        vm.serializeInt(k, "caller_delta1", obs.delta1);
        vm.serializeInt(k, "event_delta0", int256(event0));
        vm.serializeInt(k, "event_delta1", int256(event1));
        vm.serializeUint(k, "event_fee_pips", eventFee);
        vm.serializeInt(k, "caller_delta0_settled", obs.delta0Settled);
        vm.serializeInt(k, "caller_delta1_settled", obs.delta1Settled);
        vm.serializeUint(k, "nonzero_before_swap", obs.nonzeroBeforeSwap);
        vm.serializeUint(k, "nonzero_at_swap", obs.nonzeroAtSwap);
        vm.serializeUint(k, "nonzero_after_settlement", obs.nonzeroAfterSettlement);
        vm.serializeBool(k, "unlocked_at_swap", obs.unlockedAtSwap);
        vm.serializeBool(k, "unlocked_after", manager.isUnlocked());
        vm.serializeBool(k, "before_swap_hook_observed", true);
        vm.serializeBool(k, "after_swap_hook_observed", true);
        vm.serializeBool(k, "swap_log_observed", seenSwap);
        vm.serializeUint(k, "sqrt_price_before_x96", priceBefore);
        vm.serializeUint(k, "sqrt_price_after_x96", obs.priceAfter);
        vm.serializeInt(k, "tick_before", tickBefore);
        vm.serializeInt(k, "tick_after", obs.tickAfter);
        vm.serializeUint(k, "liquidity_before", liquidityBefore);
        vm.serializeUint(k, "liquidity_after", obs.liquidityAfter);
        vm.serializeUint(k, "trader0_before", trader0Before);
        vm.serializeUint(k, "trader0_after", trader0After);
        vm.serializeUint(k, "trader1_before", trader1Before);
        vm.serializeUint(k, "trader1_after", trader1After);
        vm.serializeUint(k, "vault0_before", vault0Before);
        vm.serializeUint(k, "vault0_after", vault0After);
        vm.serializeUint(k, "vault1_before", vault1Before);
        string memory json = vm.serializeUint(k, "vault1_after", vault1After);
        vm.writeJson(json, ".forge-snapshots/mathcan_chtr08_foundry.json");
    }
}
