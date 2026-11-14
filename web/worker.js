// The scanner of this repository, run in the browser. This worker loads Pyodide (CPython compiled to
// WebAssembly), copies tools/exitproof.py, tools/rpc.py, tools/token_check.py and the data files they read into
// its file system, and calls the same functions as the command line. Nothing is re-implemented in JavaScript:
// the stage a visitor sees is computed by the code that tools/selftest.py checks.
//
// The Python code makes blocking HTTP calls (urllib). In a worker a blocking XMLHttpRequest is allowed, so
// urllib.request.urlopen is replaced by one. Every request goes from the visitor's browser straight to a public
// NEAR RPC endpoint or to the deployment-history API; this page has no server of its own.

const PYODIDE = 'https://cdn.jsdelivr.net/pyodide/v0.26.4/full/';
const ROOT = new URL('..', self.location.href).href; // the root of the repository, as it is served

const BOOT = `
import io, json, sys, urllib.error, urllib.request
from js import XMLHttpRequest, Uint8Array

class _Answer:
    def __init__(self, body): self._body = body
    def read(self): return self._body
    def __enter__(self): return self
    def __exit__(self, *a): return False

def _urlopen(req, timeout=30, **kw):
    """urllib.request.urlopen for a worker: one blocking request, bytes back, HTTP errors as urllib raises them."""
    url = req.full_url if hasattr(req, "full_url") else str(req)
    data = getattr(req, "data", None)
    x = XMLHttpRequest.new()
    x.open("POST" if data is not None else "GET", url, False)
    x.responseType = "arraybuffer"
    x.timeout = int((timeout or 30) * 1000)   # a stalled endpoint ends as an error, and rpc.py tries the next
    for k, v in (getattr(req, "headers", None) or {}).items():
        if k.lower() != "user-agent":          # a browser sets its own and refuses another
            x.setRequestHeader(k, v)
    try:
        x.send(Uint8Array.new(data) if data is not None else None)
    except Exception as e:                      # no network, a refused connection, a blocked request
        raise urllib.error.URLError(str(e)[:160])
    body = bytes(Uint8Array.new(x.response).to_py()) if x.response is not None else b""
    if x.status == 0:
        raise urllib.error.URLError("no answer")
    if x.status >= 400:
        raise urllib.error.HTTPError(url, x.status, x.statusText or f"HTTP Error {x.status}", None, io.BytesIO(body))
    return _Answer(body)

urllib.request.urlopen = _urlopen
sys.path.insert(0, "/repo/tools")
import rpc, exitproof, token_check

def answer(kind, account, network, detail):
    """The same statuses as tools/mcp_server.py: ok, not_found, unreadable, error. An unread chain is never a verdict."""
    rpc.use_network(network)
    try:
        if kind == "exit":
            full = detail == "full"
            rep = exitproof.scan(account, history=full, controllers=full)
            if "error" in rep:
                status = "not_found" if rep["error"].startswith("account not found") else "bad_argument"
                return json.dumps({"status": status, "error": rep["error"]})
            return json.dumps({"status": "ok", "detail": detail, "view": exitproof.public_view(rep),
                               "report": exitproof.render(rep)}, default=str)
        r = token_check.check(account)
        if "error" in r:
            status = "not_found" if r["error"].startswith("account not found") else "bad_argument"
            return json.dumps({"status": status, "error": r["error"]})
        return json.dumps({"status": "ok", "view": r, "report": token_check.render(r)}, default=str)
    except exitproof.RpcUnavailable as e:
        return json.dumps({"status": "unreadable", "error": str(e)[:200]})
    except Exception as e:
        return json.dumps({"status": "error", "error": f"{type(e).__name__}: {str(e)[:200]}"})
`;

let pyodide = null;

async function boot() {
  postMessage({ progress: 'Loading Python for the browser (about 10 MB, once per visit)…' });
  importScripts(PYODIDE + 'pyodide.js');
  const py = await loadPyodide({ indexURL: PYODIDE });
  postMessage({ progress: 'Loading the scanner of this repository…' });
  const files = await (await fetch(ROOT + 'web/files.json')).json();
  for (const f of files) {
    const res = await fetch(ROOT + f);
    if (!res.ok) throw new Error(`${f}: HTTP ${res.status}`);
    const path = '/repo/' + f;
    py.FS.mkdirTree(path.slice(0, path.lastIndexOf('/')));
    py.FS.writeFile(path, new Uint8Array(await res.arrayBuffer()));
  }
  py.runPython(BOOT);
  pyodide = py;
  postMessage({ ready: true });
}

const booting = boot().catch((e) => {
  postMessage({ failed: `The scanner could not start: ${String(e.message || e)}` });
  throw e;
});

onmessage = async (e) => {
  const { id, kind, account, network, detail } = e.data;
  try {
    await booting;
    const out = pyodide.globals.get('answer')(kind, account, network, detail);
    postMessage({ id, answer: JSON.parse(out) });
  } catch (err) {
    postMessage({ id, answer: { status: 'error', error: String(err.message || err).slice(0, 300) } });
  }
};
