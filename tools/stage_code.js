// Sends the bytes of a wasm file as the argument of up_stage_code (too long for a command-line argument).
// usage: NODE_PATH=$(npm root -g)/near-cli/node_modules node tools/stage_code.js <contract> <signer> <wasm> <network>
// Signs with the signer's key from ~/.near-credentials/<network>/.
const nearAPI = require('near-api-js');
const fs = require('fs');
const os = require('os');

(async () => {
  const [contract, signer, wasm, network] = process.argv.slice(2);
  const keyStore = new nearAPI.keyStores.UnencryptedFileSystemKeyStore(os.homedir() + '/.near-credentials');
  const near = await nearAPI.connect({ networkId: network, nodeUrl: `https://rpc.${network}.fastnear.com`, keyStore });
  const account = await near.account(signer);
  const r = await account.functionCall({
    contractId: contract, methodName: 'up_stage_code', args: fs.readFileSync(wasm),
    gas: '300000000000000', attachedDeposit: '0',
  });
  console.log('Transaction Id', r.transaction.hash);
})().catch((e) => { console.error('Error', String(e).slice(0, 400)); process.exit(1); });
