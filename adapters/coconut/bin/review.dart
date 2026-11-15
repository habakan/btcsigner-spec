// Coconut Vault's review of a PSBT, one JSON request per line on stdin and one verdict per line on stdout.
//
// coconut_lib does the work, as in the app. What the app does around it is followed from coconut_vault
// (MIT, Copyright (c) 2024 Nonce Lab, Inc.): the vault the user picked has to be able to sign
// (isolates/sign_isolates.dart, canSignToPsbtWith*), then the confirmation screen sorts the outputs
// (providers/view_model/airgap/psbt_confirmation_view_model.dart), then it signs.
import 'dart:convert';
import 'dart:io';
import 'dart:typed_data';

import 'package:coconut_lib/coconut_lib.dart';

const mnemonic = 'abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon abandon about';
final Uint8List words = Uint8List.fromList(utf8.encode(mnemonic));
final Map<String, Object> vaults = {};

/// A single-sig P2WPKH vault, the only single-sig kind the app makes, or a P2WSH multisig vault
Object vaultFor(Map config) {
  final key = jsonEncode(config);
  return vaults.putIfAbsent(key, () {
    if (config['members'] == null) return SingleSignatureVault.fromMnemonic(words, addressType: AddressType.p2wpkh);
    final keyStores = (config['members'] as List).map<KeyStore>((m) => m['ours'] == true
        ? KeyStore.fromMnemonic(words, AddressType.p2wsh)
        : KeyStore.fromExtendedPublicKey(m['xpub'], (m['fp'] as String).toUpperCase())).toList();
    return MultisignatureVault.fromKeyStoreList(keyStores, 2);
  });
}

/// sign_isolates.dart, _isMultisigInputConsistentWithVault
bool consistent(MultisignatureVault vault, PsbtInput input) {
  if (input.witnessScript == null) return false;
  if (vault.requiredSignature != input.requiredSignature ||
      vault.keyStoreList.length != input.derivationPathList.length) {
    return false;
  }
  final ours = vault.keyStoreList.map((e) => e.masterFingerprint.toUpperCase()).toSet();
  final theirs = input.derivationPathList.map((e) => e.masterFingerprint.toUpperCase()).toSet();
  if (ours.length != theirs.length || !ours.containsAll(theirs)) return false;
  return vault.getWitnessScript(input.derivationPathList.first.path) == input.witnessScript!.rawSerialize();
}

bool canSign(Object vault, String psbt) {
  if (vault is SingleSignatureVault) return vault.hasPublicKeyInPsbt(psbt);
  final multi = vault as MultisignatureVault;
  if (!multi.keyStoreList.every((k) => k.hasPublicKeyInPsbt(psbt))) return false;
  return Psbt.parse(psbt).inputs.every((input) => consistent(multi, input));
}

Map<String, Object?> fail(String stage, Object e) =>
    {'error': stage, 'detail': '${e.runtimeType}: $e'.substring(0, '${e.runtimeType}: $e'.length.clamp(0, 120))};

Map<String, Object?> review(String psbt, Map config) {
  final vault = vaultFor(config);
  final WalletBase wallet = vault as WalletBase;
  final Psbt parsed;
  try {
    parsed = Psbt.parse(psbt);
    if (!canSign(vault, psbt)) return {'error': 'cannot sign'};
  } catch (e) {
    return fail('parse', e);
  }
  final ours = <Map<String, Object>>[];
  int input = 0, spend = 0, change = 0;
  try {
    for (final i in parsed.inputs) {
      input += i.witnessUtxo!.amount;
    }
    for (var n = 0; n < parsed.outputs.length; n++) {
      final o = parsed.outputs[n];
      if (o.isOwnedBy(wallet)) {
        ours.add({'index': n, 'verified': true});
        change += o.outAmount!;
      }
    }
    // The screen's own figures: what it sends (change excluded, our receive addresses included) and the fee
    final selfReceive = parsed.outputs.where((o) => o.isOwnedBy(wallet) && !o.isChange(wallet)).fold<int>(0, (a, o) => a + o.outAmount!);
    spend = parsed.sendingAmount(wallet) - selfReceive;
    final fee = parsed.fee;
    try {
      if (vault is SingleSignatureVault) {
        vault.addSignatureToPsbt(psbt);
      } else {
        KeyStore.fromMnemonic(words, AddressType.p2wsh).addSignatureToPsbt(psbt, AddressType.p2wsh);
      }
    } catch (e) {
      return fail('sign', e);
    }
    final addresses = <Map<String, Object>>[];
    for (var n = 0; n < parsed.outputs.length; n++) {
      try {
        addresses.add({'index': n, 'address': parsed.outputs[n].outAddress});
      } catch (_) {}
    }
    return {
      'ok': {'input': '$input', 'spend': '$spend', 'change': '$change', 'fee': '$fee', 'outputs': ours, 'warnings': [],
        'addresses': addresses}
    };
  } catch (e) {
    return fail('review', e);
  }
}

void main() {
  NetworkType.setNetworkType(NetworkType.mainnet);
  for (String? line; (line = stdin.readLineSync()) != null;) {
    final req = jsonDecode(line!) as Map;
    stdout.writeln(jsonEncode(review(req['psbt'] as String, req['config'] as Map)));
  }
}
