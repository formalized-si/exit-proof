"""Derives the second mock token from the first: a standard transfer, but a malformed value returned to the
caller of ft_transfer_call for some amounts. It does NOT follow NEP-141; it exists to exercise the branches of
the Intents contract that read a token's reply."""
import os, re, shutil, sys
src, dst = sys.argv[1], sys.argv[2]
shutil.rmtree(dst, ignore_errors=True)
shutil.copytree(src, dst, ignore=shutil.ignore_patterns("target", "out"))
p = os.path.join(dst, "src/lib.rs"); s = open(p).read()
a = s.index("    #[payable]\n    fn ft_transfer_call(")
b = s.index("    fn ft_total_supply")
s = s[:a] + '''    #[payable]
    fn ft_transfer_call(
        &mut self,
        receiver_id: AccountId,
        amount: U128,
        memo: Option<String>,
        msg: String,
    ) -> PromiseOrValue<U128> {
        self.token.ft_transfer_call(receiver_id, amount, memo, msg)
    }

''' + s[b:]
a = s.index("#[near]\nimpl FungibleTokenResolver for Contract {")
m = re.compile(r"^}\n", re.M).search(s, a)
s = s[:a] + '''#[near]
impl Contract {
    /// MOCK, NOT NEP-141: the settlement is the standard one, but the value handed back to the caller of
    /// ft_transfer_call is malformed for three amounts out of four.
    #[private]
    pub fn ft_resolve_transfer(&mut self, sender_id: AccountId, receiver_id: AccountId, amount: U128) {
        let (used_amount, burned_amount) =
            self.token.internal_ft_resolve_transfer(&sender_id, receiver_id, amount);
        if burned_amount > 0 {
            log!("Account @{} burned {}", sender_id, burned_amount);
        }
        let reply: Vec<u8> = match amount.0 % 4 {
            0 => format!("\\"{}\\"", used_amount).into_bytes(),
            1 => b"\\"not a number\\"".to_vec(),
            2 => format!("\\"{}\\"", "9".repeat(60)).into_bytes(),
            _ => b"12".to_vec(),
        };
        env::value_return(&reply);
    }
}
''' + s[m.end():]
s = s.replace("    FungibleToken, FungibleTokenCore, FungibleTokenResolver,\n", "    FungibleToken, FungibleTokenCore,\n")
s = s.replace("use near_contract_standards::fungible_token::receiver::ext_ft_receiver;\n", "")
s = s.replace("use near_contract_standards::fungible_token::resolver::ext_ft_resolver;\n", "")
s = s.replace("    AccountId, BorshStorageKey, Gas, NearToken, PanicOnDefault, PromiseOrValue, env, log, near,\n",
              "    AccountId, BorshStorageKey, NearToken, PanicOnDefault, PromiseOrValue, env, log, near,\n")
s = s.replace("MOCK for the backing monitor: the near-sdk fungible-token example with a fee kept on\nft_transfer_call that the receiver is not told about. It does NOT follow NEP-141.",
              "MOCK for the replay of reply handling: the near-sdk fungible-token example whose ft_transfer_call\nhands back a malformed value for three amounts out of four. It does NOT follow NEP-141.")
open(p, "w").write(s)
print("written", p, len(s.splitlines()), "lines")
