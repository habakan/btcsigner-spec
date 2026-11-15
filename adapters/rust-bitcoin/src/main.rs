//! rust-bitcoin's handling of a PSBT, one JSON request per line on stdin and one verdict per line on stdout.
//! It is a library with no review screen: what a wallet built on it shows is taken to be `Psbt::fee()`
//! once `Psbt::sign()` has signed with the test seed, and each output's `Address::from_script`.
use std::io::{self, BufRead, Write};
use std::str::FromStr;

use bitcoin::bip32::Xpriv;
use bitcoin::secp256k1::Secp256k1;
use bitcoin::{Address, Network, Psbt};
use serde_json::{json, Value};

fn review(b64: &str, master: &Xpriv) -> Value {
    let secp = Secp256k1::new();
    let mut psbt = match Psbt::from_str(b64) {
        Ok(p) => p,
        Err(e) => return json!({ "error": "parse", "detail": e.to_string() }),
    };
    let signed = match psbt.sign(master, &secp) {
        Ok(keys) => keys,
        Err((keys, errors)) if keys.is_empty() => {
            let detail = errors.values().next().map(|e| e.to_string()).unwrap_or_default();
            return json!({ "error": "sign", "detail": detail });
        }
        Err((keys, _)) => keys,
    };
    if signed.is_empty() {
        return json!({ "error": "sign", "detail": "nothing signed" });
    }
    let fee = match psbt.fee() {
        Ok(f) => f.to_sat(),
        Err(e) => return json!({ "error": "fee", "detail": e.to_string() }),
    };
    let spend: u64 = psbt.unsigned_tx.output.iter().map(|o| o.value.to_sat()).sum();
    let addresses: Vec<Value> = psbt.unsigned_tx.output.iter().enumerate()
        .filter_map(|(index, o)| Address::from_script(&o.script_pubkey, Network::Bitcoin).ok()
            .map(|a| json!({ "index": index, "address": a.to_string() })))
        .collect();
    json!({ "ok": { "input": (fee + spend).to_string(), "spend": spend.to_string(), "change": "0",
        "fee": fee.to_string(), "outputs": [], "warnings": [], "addresses": addresses } })
}

fn main() {
    let words = "abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about";
    let seed = bip39::Mnemonic::parse(words).expect("test mnemonic").to_seed("");
    let master = Xpriv::new_master(Network::Bitcoin, &seed).expect("master key");
    std::panic::set_hook(Box::new(|_| {}));
    let stdout = io::stdout();
    for line in io::stdin().lock().lines() {
        let req: Value = serde_json::from_str(&line.expect("stdin")).expect("request");
        // Psbt::sign() panics on some PSBTs (a non_witness_utxo vout out of range); report it as a refusal
        let b64 = req["psbt"].as_str().unwrap_or_default().to_string();
        let verdict = std::panic::catch_unwind(|| review(&b64, &master))
            .unwrap_or_else(|_| json!({ "error": "panic", "detail": "Psbt::sign panicked" }));
        writeln!(stdout.lock(), "{}", verdict).expect("stdout");
    }
}
