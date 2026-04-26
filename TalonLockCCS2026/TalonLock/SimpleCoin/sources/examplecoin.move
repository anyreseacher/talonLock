module ctf::ExampleCoin {
    use iota::coin::{Self, TreasuryCap};

    public struct EXAMPLECOIN has drop {}

    public struct MintCoin<phantom EXAMPLECOIN> has key, store {
        id: UID,
        cap: TreasuryCap<EXAMPLECOIN>,
    }

    #[allow(lint(self_transfer))]
   fun init(witness: EXAMPLECOIN, ctx: &mut TxContext) {
        // Get a treasury cap for the coin and give it to the transaction sender
        let (treasury_cap, metadata) = coin::create_currency<EXAMPLECOIN>(
            witness,
            1,
            b"EXAMPLECOIN",
            b"CTF A Coin",
            b"Token for the Test",
            option::none(),
            ctx
        );
        let mint = MintCoin<EXAMPLECOIN> {
            id: object::new(ctx),
            cap: treasury_cap,
        };
        transfer::share_object(mint);
        transfer::public_freeze_object(metadata);
    }

    /// Freeze the MintCoin object and the corresponding cap
    public fun freeze_object<EXAMPLECOIN>(mut tofreeze: MintCoin<EXAMPLECOIN>) {
        let MintCoin<EXAMPLECOIN> { id: ida, cap: capa } = tofreeze;
        object::delete(ida);  // Delete object after use
        transfer::public_freeze_object(capa);
    }

    /// Mint new tokens and transfer them to the vesting contract or user
    public fun mint<EXAMPLECOIN>(mut mint:  MintCoin<EXAMPLECOIN>, amount: u64, ctx: &mut TxContext) {
        coin::mint_and_transfer(&mut mint.cap, amount, tx_context::sender(ctx), ctx);
        transfer::share_object(mint);
    }

    /// Mint new tokens and transfer them to the vesting contract or user
    public fun mint_for_vester<EXAMPLECOIN>(mut mint: MintCoin<EXAMPLECOIN>, amount: u64, ctx: &mut TxContext) {
        coin::mint_and_transfer(&mut mint.cap, amount, tx_context::sender(ctx), ctx);
        let MintCoin<EXAMPLECOIN> { id: ida, cap: capa } = mint;
        object::delete(ida);  // Delete object to prevent reuse
        transfer::public_freeze_object(capa);
    }
/*
    /// Placeholder function to represent the total amount to be vested
    public fun total_tobe_vested_amount<EXAMPLECOIN>(mut mint: MintCoin<EXAMPLECOIN>): u64 {
        10  // Dummy implementation, to be replaced with actual logic
    }*/
}
