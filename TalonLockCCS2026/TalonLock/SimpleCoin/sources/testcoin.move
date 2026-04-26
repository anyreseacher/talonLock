module ctf::TestCoin {
    use iota::coin::{Self, TreasuryCap};

    public struct TESTCOIN has drop {}

    public struct MintCoin<phantom TESTCOIN> has key, store {
        id: UID,
        cap: TreasuryCap<TESTCOIN>,
    }

    #[allow(lint(self_transfer))]
   fun init(witness: TESTCOIN, ctx: &mut TxContext) {
        // Get a treasury cap for the coin and give it to the transaction sender
        let (treasury_cap, metadata) = coin::create_currency<TESTCOIN>(
            witness,
            1,
            b"TESTCOIN",
            b"TEST A Coin",
            b"Token for the Test",
            option::none(),
            ctx
        );
        let mint = MintCoin<TESTCOIN> {
            id: object::new(ctx),
            cap: treasury_cap,
        };
        transfer::share_object(mint);
        transfer::public_freeze_object(metadata);
    }

    /// Freeze the MintCoin object and the corresponding cap
    public fun freeze_object<TESTCOIN>(mut tofreeze: MintCoin<TESTCOIN>) {
        let MintCoin<TESTCOIN> { id: ida, cap: capa } = tofreeze;
        object::delete(ida);  // Delete object after use
        transfer::public_freeze_object(capa);
    }

    /// Mint new tokens and transfer them to the vesting contract or user
    public fun mint<TESTCOIN>(mut mint:  MintCoin<TESTCOIN>, amount: u64, ctx: &mut TxContext) {
        coin::mint_and_transfer(&mut mint.cap, amount, tx_context::sender(ctx), ctx);
        transfer::share_object(mint);
    }

    /// Mint new tokens and transfer them to the vesting contract or user
    public fun mint_for_vester<TESTCOIN>(mut mint: MintCoin<TESTCOIN>, amount: u64, ctx: &mut TxContext) {
        coin::mint_and_transfer(&mut mint.cap, amount, tx_context::sender(ctx), ctx);
        let MintCoin<TESTCOIN> { id: ida, cap: capa } = mint;
        object::delete(ida);  // Delete object to prevent reuse
        transfer::public_freeze_object(capa);
    }
}
