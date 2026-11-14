# The config format

A config is one JSON file. It tells the kit how to bring your token to life in the simulator:
which account the wasm is deployed on, who calls the init method with which arguments, which calls
follow, and which accounts end up holding tokens. The wasm itself is not named in the config; it is
the first argument of `certify.sh`.

A misspelled or unknown key is an error, not a silent default. `./try-config.sh token.wasm
config.json` validates the file, makes the calls and prints what happened.

The shortest config, for a token whose init gives the whole supply to one account:

```json
{
  "init": {
    "method": "new",
    "args": {"owner_id": "owner.near", "total_supply": "1000000000000000000000000000000",
             "metadata": {"spec": "ft-1.0.0", "name": "Test", "symbol": "T", "decimals": 18}}
  }
}
```

## The simulated world

Every run starts from the same world. Your config adds to it.

| Account | What it is |
|---|---|
| `owner.near`, `alice.near`, `bob.near`, `c1.near`, `aaa…a.near` (59 letters `a`, a 64-character id) | the five users; each holds 1,000,000 NEAR. They send every kind of call to the token |
| `recv1.near`, `recv2.near` | two receiver contracts. Their `ft_on_transfer` is scripted per transfer: return a number, return unparsable bytes, fail, call the token back, burn all its gas |
| `evil.near` | a contract that tries to run the token's settlement callback as the callback of its own promise |
| `ghost.near` | a name without an account; a target for transfers and registrations |
| `token.near` (or `token_account`) | your token; holds 50 NEAR (or `token_near`) |
| `Bad!Id`, `x` | two invalid account ids, used only as transfer targets |

All of these are *watched*: after every block the kit reads `ft_balance_of` for each of them and
`ft_total_supply`. The monitors compare the supply with the sum over the watched accounts, so every
account that can hold tokens must be watched (see `track`).

## Top-level keys

All keys are optional except that a token which needs an init call needs `init`.

| Key | Type | Default | Meaning |
|---|---|---|---|
| `description` | string | none | Free text for people. The kit does not read it |
| `token_account` | account id | `token.near` | The account the wasm is deployed on. Change it when the token reads its own name, for example a factory-created token that only accepts calls from its parent account: `tok.factory.near` with `factory.near` in `accounts` |
| `accounts` | list of account ids | `[]` | Extra accounts to create, each with 1,000,000 NEAR: a factory, a controller, a treasury, a minter. They can be callers in `init` and `setup`, they are watched, and they can be the `funder` |
| `init` | call | none | The init call. See "Calls" below. Without `init` the token is used as deployed |
| `setup` | list of calls | `[]` | Calls made after `init`, in order, before any trace starts: minting, distribution to the test users, storage registration, switching a role. A failed call stops the run unless it has `may_fail` |
| `stubs` | list of stubs | `[]` | Stand-ins for other contracts your token calls during init or setup (an exchange, a price oracle). See "Stubs" below. Stub accounts are watched |
| `funder` | account id | the user account with the largest balance after the set-up | The account that hands out tokens to the other users at the start of every trace. Must be one of the five users or listed in `accounts`, and must hold tokens after the set-up. Name it when the largest holder should not be the one that distributes |
| `track` | list of account ids | `[]` | Further accounts to watch: any account that holds tokens after the set-up, or can receive them later, and is not already watched (a vesting account, a fee collector, a burn address). They need not exist as accounts |
| `token_near` | integer | `50` | NEAR balance of the token account at creation |
| `timestamp_ns` | integer | the simulator's default | Block timestamp at the start, in nanoseconds, for tokens whose behaviour depends on time |
| `transfer_memos` | list of strings | `[]` | Memos the generator attaches to some transfers (to a quarter of them, and to every transfer sent to the token account itself). For tokens whose behaviour depends on the memo |
| `resolve_method` | string | `ft_resolve_transfer` | The name of the token's settlement callback, when it is not the standard one |

## Calls (`init` and the entries of `setup`)

| Key | Type | Default | Meaning |
|---|---|---|---|
| `method` | string | required | The method to call |
| `caller` | account id | the token account | Who sends the call. Must exist: a user, a receiver, an entry of `accounts`, a stub account or the token account. This is how a factory-only or owner-only method is called |
| `receiver` | account id | the token account | `setup` only: the contract that is called, when it is not the token (for example a stub that calls the token back) |
| `args` | any JSON value | `{}` | The arguments, sent as JSON. A JSON string is sent as it is, byte for byte |
| `args_base64` | string | none | Raw argument bytes in base64, for methods that take Borsh. Use it instead of `args` |
| `deposit` | string | `"0"` | Attached deposit in yoctoNEAR, as a decimal string (`"1"`, `"1250000000000000000000"`) |
| `gas_tgas` | integer | the simulator's default | Gas for the call in Tgas, 1 to 1000 |
| `may_fail` | boolean | `false` | `setup` only: a failure of this call does not stop the run |

## Stubs

```json
"stubs": [{"account": "pool.near", "methods": {"ft_on_transfer": "0", "add_pool": 7}}]
```

A stub is a contract at `account` that answers each listed method with the given JSON value and
fails on any other method. It exists so that a token whose init or setup calls another contract can
complete. A stub holds 1,000,000 NEAR and is watched.

## How the generator learns who holds tokens

1. After `init` and `setup`, the kit reads `ft_total_supply` and `ft_balance_of` of every watched
   account. `try-config.sh` prints both.
2. The supply must be positive and must equal the sum of the watched balances. If it does not, the
   run stops as INCONCLUSIVE and names the two numbers: add the missing holder to `track` (or to
   `accounts` if it also has to send calls). If every holder is listed and the numbers still differ,
   your init creates supply that no account holds, which is a violation of P1.
3. The `funder` (named, or the user account with the largest balance) registers nobody and decides
   nothing else: at the start of each trace most accounts are registered with `storage_deposit`,
   then the funder sends a random share of its balance to most of them with `ft_transfer`. From
   then on every account acts for itself.

If no user account holds tokens after the set-up (the supply sits on the token account, on a stub
or on a tracked name), the run stops as INCONCLUSIVE and says so: add a `setup` call that moves
tokens to a user account, or make a user account the caller that receives the supply.

## Worked shapes

| Your token | What the config needs | Example |
|---|---|---|
| The init mints the supply to an account you name | `init` with that account set to `owner.near` | `examples/reference.json`, `examples/tkn-factory-token.json`, `examples/ref-token.json`, `examples/default-meta-token.json` |
| The supply goes to a treasury which then distributes | `accounts` with the treasury, `setup` with the registrations and transfers, `track` for holders that are not actors | `examples/reference-distribution.json` |
| Only a factory (the parent account) may call the init, and tokens are minted afterwards | `token_account` under the factory's name, the factory in `accounts`, `init.caller`, then `setup`: `storage_deposit` for the receiver and the mint call sent by the factory | `examples/factory-minted.json` |
| The init is sent by a launch platform and calls an exchange contract | the platform in `accounts` and as `init.caller`, a stub for the exchange | `examples/launchpad-token.json` |
| The init takes Borsh arguments | `args_base64` | `tests/setup/raw-args.json` (raw bytes; the format of the bytes is up to the token) |
| The settlement callback has its own name | `resolve_method` | `tests/setup/every-field.json` uses the key with the standard name |

`tests/setup/every-field.json` is a config that uses every key of the format at once.

## What a config must not be used for

The monitors judge the standard interface. A config that never mints, or that leaves a switch of
your token off (a transfer fee, a pause, a blocklist), certifies only the behaviour with that switch
off. The certificate lists every exported method that no call reached, so the gap is visible; to
cover a switch, turn it on in `setup` and certify again with that config.
