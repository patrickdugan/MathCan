// SPDX-License-Identifier: UNLICENSED
pragma solidity ^0.8.24;

// Installed under test/ of pinned Uniswap/v4-core. Reuses the CHTR-08 router,
// which performs the real PoolManager.unlock / swap / settle / take sequence.
import {Deployers} from "./utils/Deployers.sol";
import {Vm} from "forge-std/Vm.sol";
import {MockERC20} from "solmate/src/test/utils/mocks/MockERC20.sol";
import {IPoolManager} from "../src/interfaces/IPoolManager.sol";
import {IHooks} from "../src/interfaces/IHooks.sol";
import {Hooks} from "../src/libraries/Hooks.sol";
import {StateLibrary} from "../src/libraries/StateLibrary.sol";
import {TransientStateLibrary} from "../src/libraries/TransientStateLibrary.sol";
import {TickMath} from "../src/libraries/TickMath.sol";
import {Currency, CurrencyLibrary} from "../src/types/Currency.sol";
import {PoolKey} from "../src/types/PoolKey.sol";
import {PoolId, PoolIdLibrary} from "../src/types/PoolId.sol";
import {SwapParams, ModifyLiquidityParams} from "../src/types/PoolOperation.sol";
import {MockHooks} from "../src/test/MockHooks.sol";
import {MathCanObservedRouter} from "./MathCanCHTR08.t.sol";

contract MathCanCHTR09 is Deployers {
    using StateLibrary for IPoolManager;
    using TransientStateLibrary for IPoolManager;
    using PoolIdLibrary for PoolKey;
    using CurrencyLibrary for Currency;

    string internal constant CORE_COMMIT = "bea7f6d1c11cd5dc4f0d5151ffa37a1c239feee6";
    uint256 internal constant GROSS_IN = 1e16;
    bytes32 internal constant NONZERO_SLOT =
        0x7d4b3164c6e45b97e7d87b7125a44c5828d005af88f9d751cfd78729c5d99a0b;
    MathCanObservedRouter internal probe;
    MockHooks internal hook;

    function setUp() public {
        deployFreshManagerAndRouters();
        deployMintAndApprove2Currencies();
        address hookAddress = address(uint160(Hooks.BEFORE_SWAP_FLAG | Hooks.AFTER_SWAP_FLAG));
        MockHooks impl = new MockHooks();
        vm.etch(hookAddress, address(impl).code); // deterministic test-only hook deployment
        hook = MockHooks(hookAddress);
        (key,) = initPoolAndAddLiquidity(currency0, currency1, IHooks(hookAddress), 3000, SQRT_PRICE_1_1);

        // An adjacent liquidity range crosses the initialized -120 boundary.
        // With a zero-for-one trade, the pool exits [-120,120) at -120 and
        // enters [-240,-120), increasing active liquidity from 1e18 to 2e18.
        ModifyLiquidityParams memory adjacent = ModifyLiquidityParams({
            tickLower: -240, tickUpper: -120, liquidityDelta: 2e18, salt: 0
        });
        modifyLiquidityRouter.modifyLiquidity(key, adjacent, ZERO_BYTES);
        probe = new MathCanObservedRouter(manager);
        MockERC20(Currency.unwrap(currency0)).approve(address(probe), type(uint256).max);
        MockERC20(Currency.unwrap(currency1)).approve(address(probe), type(uint256).max);
    }

    function test_chtr09_ordered_manager_tstores_and_multitick() public {
        PoolId id = key.toId();
        (uint160 beforePrice, int24 beforeTick,,) = manager.getSlot0(id);
        uint128 beforeLiquidity = manager.getLiquidity(id);
        uint256 t0 = currency0.balanceOf(address(this));
        uint256 t1 = currency1.balanceOf(address(this));
        uint256 b0 = currency0.balanceOf(address(manager));
        uint256 b1 = currency1.balanceOf(address(manager));
        require(beforeTick == 0 && beforePrice == SQRT_PRICE_1_1, "bad starting price/tick");
        require(beforeLiquidity == 1e18, "bad starting liquidity");

        SwapParams memory params = SwapParams({
            zeroForOne: true,
            amountSpecified: -int256(GROSS_IN),
            sqrtPriceLimitX96: MIN_PRICE_LIMIT
        });
        vm.recordLogs();
        vm.startDebugTraceRecording();
        MathCanObservedRouter.Observation memory obs = probe.execute(key, params);
        Vm.DebugStep[] memory steps = vm.stopAndReturnDebugTraceRecording();
        Vm.Log[] memory logs = vm.getRecordedLogs();
        require(steps.length > 0, "missing opcode recording");

        bytes32[] memory pairs = new bytes32[](steps.length * 2);
        uint256 n;
        for (uint256 i = 0; i < steps.length; ++i) {
            if (steps[i].opcode != 0x5d || steps[i].contractAddr != address(manager)) continue;
            require(steps[i].stack.length >= 2, "TSTORE missing stack operands");
            // DebugStep.stack[0] is EVM top-of-stack: TSTORE(slot,value).
            pairs[2*n] = bytes32(steps[i].stack[0]);
            pairs[2*n+1] = bytes32(steps[i].stack[1]);
            ++n;
        }
        // Trim unused array capacity. The recorded count is cross-checked in Python.
        assembly ("memory-safe") { mstore(pairs, mul(n, 2)) }
        require(n >= 13, "PoolManager TSTORE stream too short");

        bytes32 signature = keccak256("Swap(bytes32,address,int128,int128,uint160,uint128,int24,uint24)");
        bool seen;
        int128 log0;
        int128 log1;
        uint160 logPrice;
        int24 logTick;
        uint128 logLiquidity;
        uint24 logFee;
        for (uint256 i=0; i<logs.length; ++i) {
            if (logs[i].emitter != address(manager) || logs[i].topics.length < 3 || logs[i].topics[0] != signature) continue;
            require(!seen && logs[i].topics[1]==PoolId.unwrap(id), "unexpected Swap log");
            require(address(uint160(uint256(logs[i].topics[2])))==address(probe), "wrong router");
            seen = true;
            (log0, log1, logPrice, logLiquidity, logTick, logFee) =
                abi.decode(logs[i].data, (int128,int128,uint160,uint128,int24,uint24));
        }
        require(seen, "no Swap log");
        require(log0==obs.delta0 && log1==obs.delta1, "emission differs from swap result");
        require(logPrice==obs.priceAfter && logTick==obs.tickAfter, "slot0 log mismatch");
        require(logLiquidity==obs.liquidityAfter && logLiquidity==2e18, "did not cross liquidity boundary");
        require(obs.tickAfter < -120 && obs.tickAfter > -240, "unexpected number of ticks crossed");
        require(obs.priceAfter < TickMath.getSqrtPriceAtTick(-120)
                && obs.priceAfter > TickMath.getSqrtPriceAtTick(-240), "target boundary violation");
        require(logFee==3000 && obs.delta0==-int256(GROSS_IN) && obs.delta1>0, "wrong fee / swap signs");
        require(obs.nonzeroAtSwap==2 && obs.nonzeroAfterSettlement==0, "nonzero count mismatch");
        require(manager.getNonzeroDeltaCount()==0 && !manager.isUnlocked(), "PoolManager relock failure");
        require(keccak256(hook.beforeSwapData())==keccak256(bytes(probe.MARKER())), "before hook missing");
        require(keccak256(hook.afterSwapData())==keccak256(bytes(probe.MARKER())), "after hook missing");
        require(int256(currency0.balanceOf(address(this))) - int256(t0)==obs.delta0, "trader0 transfer");
        require(int256(currency1.balanceOf(address(this))) - int256(t1)==obs.delta1, "trader1 transfer");
        require(int256(currency0.balanceOf(address(manager))) - int256(b0)==-obs.delta0, "vault0 transfer");
        require(int256(currency1.balanceOf(address(manager))) - int256(b1)==-obs.delta1, "vault1 transfer");

        string memory k = "mathcan_chtr09";
        vm.serializeString(k, "schema", "mathcan.chtr09.foundry-opcode.v1");
        vm.serializeString(k, "core_commit", CORE_COMMIT);
        vm.serializeAddress(k, "manager", address(manager));
        vm.serializeAddress(k, "probe_router", address(probe));
        vm.serializeAddress(k, "hook", address(hook));
        vm.serializeAddress(k, "currency0", Currency.unwrap(currency0));
        vm.serializeAddress(k, "currency1", Currency.unwrap(currency1));
        vm.serializeBytes32(k, "pool_id", PoolId.unwrap(id));
        vm.serializeBytes32(k, "manager_runtime_hash", address(manager).codehash);
        vm.serializeInt(k, "swap_amount_specified", params.amountSpecified);
        vm.serializeInt(k, "caller_delta0", obs.delta0);
        vm.serializeInt(k, "caller_delta1", obs.delta1);
        vm.serializeInt(k, "event_delta0", int256(log0));
        vm.serializeInt(k, "event_delta1", int256(log1));
        vm.serializeUint(k, "event_fee_pips", logFee);
        vm.serializeUint(k, "nonzero_at_swap", obs.nonzeroAtSwap);
        vm.serializeUint(k, "nonzero_after_settlement", obs.nonzeroAfterSettlement);
        vm.serializeUint(k, "sqrt_price_before_x96", beforePrice);
        vm.serializeUint(k, "boundary_price_x96", TickMath.getSqrtPriceAtTick(-120));
        vm.serializeUint(k, "sqrt_price_after_x96", obs.priceAfter);
        vm.serializeInt(k, "tick_before", beforeTick);
        vm.serializeInt(k, "tick_after", obs.tickAfter);
        vm.serializeUint(k, "liquidity_before", beforeLiquidity);
        vm.serializeUint(k, "liquidity_after", obs.liquidityAfter);
        vm.serializeUint(k, "trader0_before", t0);
        vm.serializeUint(k, "trader0_after", currency0.balanceOf(address(this)));
        vm.serializeUint(k, "trader1_before", t1);
        vm.serializeUint(k, "trader1_after", currency1.balanceOf(address(this)));
        vm.serializeUint(k, "vault0_before", b0);
        vm.serializeUint(k, "vault0_after", currency0.balanceOf(address(manager)));
        vm.serializeUint(k, "vault1_before", b1);
        vm.serializeUint(k, "vault1_after", currency1.balanceOf(address(manager)));
        vm.serializeBool(k, "hooks_observed", true);
        vm.serializeBool(k, "swap_log_observed", seen);
        vm.serializeUint(k, "debug_step_count", steps.length);
        vm.serializeUint(k, "manager_tstore_count", n);
        string memory json=vm.serializeBytes32(k, "manager_tstore_pairs", pairs);
        vm.writeJson(json, ".forge-snapshots/mathcan_chtr09_foundry.json");
    }
}
