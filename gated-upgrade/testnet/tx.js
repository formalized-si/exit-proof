// Sends one transaction on NEAR testnet and prints what happened as one JSON line (also appended
// to testnet/tx.jsonl). Signs with the signer's key file in ~/.near-credentials/testnet/; never
// prints key material. Refuses any network but testnet.
//
// usage: NODE_PATH=$(npm root -g)/near-cli/node_modules node testnet/tx.js <label> <command> ...
//   call <signer> <receiver> <method> <json args | @file (raw bytes) | json@file> [Tgas = 300] [deposit in NEAR = 0]
//   create <parent> <new account> <public key> <balance in NEAR>
//   deploy-init <account> <wasm file> <init method> <json args> [Tgas = 300]
//   delete-key <account> <public key>
// Exit status: 0 if the transaction's final status is a success, 1 if it failed, 2 on usage or
// transport errors.
const nearAPI = require('near-api-js');
const BN = require('bn.js');
const fs = require('fs');
const os = require('os');
const path = require('path');

const NETWORK = 'testnet';
const RPC = process.env.NEAR_TESTNET_RPC || 'https://rpc.testnet.fastnear.com';
const { transactions, utils } = nearAPI;
const tgas = (x) => new BN(x || '300').mul(new BN('1000000000000'));
const near2yocto = (x) => new BN(utils.format.parseNearAmount(x || '0'));
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

function failureText(status) {
  if (!status || status.SuccessValue !== undefined || status.SuccessReceiptId !== undefined) return null;
  const s = JSON.stringify(status.Failure || status);
  const m = s.match(/"ExecutionError":"((?:[^"\\]|\\.)*)"/);
  return m ? JSON.parse('"' + m[1] + '"') : s.slice(0, 600);
}

(async () => {
  const [label, command, ...a] = process.argv.slice(2);
  let signer, receiver, actions, what;
  if (command === 'call') {
    const [s, r, method, args, gas, deposit] = a;
    // "@file": the file's raw bytes are the arguments; "json@file": the file holds the JSON arguments
    const json = args.startsWith('json@') ? JSON.parse(fs.readFileSync(args.slice(5), 'utf8')) : null;
    const payload = args.startsWith('@') ? fs.readFileSync(args.slice(1)) : Buffer.from(JSON.stringify(json || JSON.parse(args)));
    [signer, receiver] = [s, r];
    actions = [transactions.functionCall(method, payload, tgas(gas), near2yocto(deposit))];
    what = { method, args: args.startsWith('@') ? `${payload.length} bytes of ${path.basename(args.slice(1))}` : (json ? `the JSON in ${path.basename(args.slice(5))}` : JSON.parse(args)), tgas: gas || '300', deposit_near: deposit || '0' };
  } else if (command === 'create') {
    const [parent, account, publicKey, balance] = a;
    [signer, receiver] = [parent, account];
    actions = [transactions.createAccount(), transactions.transfer(near2yocto(balance)),
               transactions.addKey(utils.PublicKey.from(publicKey), transactions.fullAccessKey())];
    what = { action: 'create account', balance_near: balance, public_key: publicKey };
  } else if (command === 'deploy-init') {
    const [account, wasm, method, args, gas] = a;
    [signer, receiver] = [account, account];
    actions = [transactions.deployContract(fs.readFileSync(wasm)),
               transactions.functionCall(method, Buffer.from(JSON.stringify(JSON.parse(args))), tgas(gas), new BN(0))];
    what = { action: 'deploy and init', wasm: path.basename(wasm), method, args: JSON.parse(args) };
  } else if (command === 'delete-key') {
    const [account, publicKey] = a;
    [signer, receiver] = [account, account];
    actions = [transactions.deleteKey(utils.PublicKey.from(publicKey))];
    what = { action: 'delete access key', public_key: publicKey };
  } else {
    console.error('usage: tx.js <label> call|create|deploy-init|delete-key ...');
    process.exit(2);
  }
  const keyStore = new nearAPI.keyStores.UnencryptedFileSystemKeyStore(path.join(os.homedir(), '.near-credentials'));
  const near = await nearAPI.connect({ networkId: NETWORK, nodeUrl: RPC, keyStore });
  const account = await near.account(signer);
  const [txHash, signedTx] = await account.signTransaction(receiver, actions);
  const hash = utils.serialize.base_encode(txHash);
  const provider = near.connection.provider;
  const bytes = Buffer.from(signedTx.encode()).toString('base64');
  let sent = false;
  for (let i = 0; i < 5 && !sent; i++) {
    try { await provider.sendJsonRpc('broadcast_tx_async', [bytes]); sent = true; } catch (e) { await sleep(1500 * (i + 1)); }
  }
  let res = null;
  for (let i = 0; i < 60 && !res; i++) {
    await sleep(2000);
    try {
      const r = await provider.sendJsonRpc('EXPERIMENTAL_tx_status', { tx_hash: hash, sender_account_id: signer, wait_until: 'FINAL' });
      if (r && r.final_execution_status === 'FINAL') res = r;
    } catch (e) { /* not known yet, or the node is still waiting: ask again */ }
  }
  const out = { label, time: new Date().toISOString(), tx: hash, signer, receiver, ...what };
  if (!res) {
    out.result = 'unknown: no final status within two minutes';
    console.log(JSON.stringify(out));
    fs.appendFileSync(path.join(__dirname, 'tx.jsonl'), JSON.stringify(out) + '\n');
    process.exit(2);
  }
  const fail = failureText(res.status);
  out.result = fail === null ? 'success' : 'failure';
  if (fail !== null) out.failure = fail;
  if (res.status.SuccessValue) out.returned = Buffer.from(res.status.SuccessValue, 'base64').toString().slice(0, 300);
  out.block_hash = res.transaction_outcome.block_hash;
  out.receipts = res.receipts_outcome.map((r) => {
    const o = { executor: r.outcome.executor_id, ok: failureText(r.outcome.status) === null, block_hash: r.block_hash };
    const f = failureText(r.outcome.status);
    if (f !== null) o.failure = f;
    if (r.outcome.logs.length) o.logs = r.outcome.logs;
    const rec = (res.receipts || []).find((x) => x.receipt_id === r.id);
    if (rec && rec.receipt && rec.receipt.Action) {
      o.predecessor = rec.predecessor_id;
      o.actions = rec.receipt.Action.actions.map((x) => (typeof x === 'string' ? x : Object.keys(x)[0] + (x.FunctionCall ? `(${x.FunctionCall.method_name})` : '')));
    }
    return o;
  });
  out.gas_burnt_tgas = (res.receipts_outcome.reduce((s, r) => s + r.outcome.gas_burnt, res.transaction_outcome.outcome.gas_burnt) / 1e12).toFixed(1);
  console.log(JSON.stringify(out));
  fs.appendFileSync(path.join(__dirname, 'tx.jsonl'), JSON.stringify(out) + '\n');
  process.exit(fail === null ? 0 : 1);
})().catch((e) => { console.error('Error', String(e).slice(0, 400)); process.exit(2); });
