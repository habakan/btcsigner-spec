# The Lean model, its proofs, and the signers and libraries compared with it. Each signer is fetched at a pinned commit
# into third_party/ by `make deps`; Coconut Vault's coconut_lib is locked by hash in adapters/coconut.
BITWASM = third_party/bitwasm-signer
BITWASM_REV = 17f2dee7828e12da99e9881da36363ec8922ddfe
SEEDSIGNER = third_party/seedsigner
SEEDSIGNER_REV = e0a80d4b33b8eb7fb1e9fd14a27b7cd11c7d2cd6
KRUX = third_party/krux
KRUX_REV = 2b20e3370169731a0d89839a4113ad9a1b732078
KRUX_EMBIT = third_party/krux-embit
KRUX_EMBIT_REV = eb6104fd85d3becabba628756cd5e1b75619f3a1
SPECTER = third_party/specter-diy
SPECTER_REV = b2d87e55338289a258ee985b26c7b064d5b49132
COLDCARD = third_party/coldcard
COLDCARD_REV = 1ba960460692fee7ac0ec42403eeec5910942710
# As Coldcard's README builds its simulator with current Apple Clang
COLDCARD_CFLAGS = -Wno-unused-but-set-variable -Wno-array-bounds -Wno-error=unknown-warning-option -Wno-error=deprecated-non-prototype -Wno-error=bitwise-instead-of-logical -Wno-unterminated-string-initialization -Wno-gnu-folding-constant
BITCOINJS = third_party/bitcoinjs-lib
BITCOINJS_REV = ab9fad5978bc1f4fb6542d1cde903d4427c3344e
MODEL = .lake/build/bin/signer-spec

all: check
.PHONY: all

# Build the model, check every proof, and the notation and digests against published vectors
check:
	lake build
	lake env lean tests/Notation.lean
	lake env lean tests/Sighash.lean
	lake env lean tests/Message.lean
	lake env lean tests/Address.lean
	lake env lean tests/Txid.lean
	lake env lean tests/Mnemonic.lean
	lake env lean tests/Psbt.lean
	lake env lean tests/Multisig.lean
	lake env lean tests/OrD.lean
	lake env lean tests/Review.lean
.PHONY: check

# The manual, in its own Lake package so the model keeps no dependencies (manual/_out/html-multi)
docs:
	cd manual && lake exe manual
.PHONY: docs

$(MODEL): Main.lean $(wildcard SignerSpec/*.lean)
	lake build signer-spec

clone = test -d $(1) || git clone --filter=blob:none $(2) $(1); cd $(1) && git checkout -q --detach $(3)
# The PSBTs every case starts from, from bitwasm-signer's committed files and Core's rpc_psbt.json (Python only)
seeds:
	mkdir -p third_party
	$(call clone,$(BITWASM),https://github.com/bitwasm-project/bitwasm-signer.git,$(BITWASM_REV))
	$(MAKE) -C $(BITWASM)/parser build/vectors/own_p2wpkh_1in.psbt
.PHONY: seeds

deps: seeds
	mkdir -p build
	test -d $(BITWASM)/third_party/secp256k1 || $(MAKE) -C $(BITWASM) deps
	$(MAKE) -C $(BITWASM) all
	$(call clone,$(SEEDSIGNER),https://github.com/SeedSigner/seedsigner.git,$(SEEDSIGNER_REV))
	uv venv -q -p 3.12 build/venv-seedsigner
	uv pip install -q -p build/venv-seedsigner/bin/python --require-hashes -r adapters/requirements.txt
	$(call clone,$(KRUX),https://github.com/selfcustody/krux.git,$(KRUX_REV))
	$(call clone,$(KRUX_EMBIT),https://github.com/diybitcoinhardware/embit.git,$(KRUX_EMBIT_REV))
	uv venv -q -p 3.12 build/venv-krux
	uv pip install -q -p build/venv-krux/bin/python $(KRUX_EMBIT)
	$(call clone,$(SPECTER),https://github.com/cryptoadvance/specter-diy.git,$(SPECTER_REV))
	cd $(SPECTER) && git submodule update --init --depth 1 f469-disco && git -C f469-disco submodule update --init --depth 1 libs/common/embit
	uv venv -q -p 3.12 build/venv-specter
	$(call clone,$(COLDCARD),https://github.com/Coldcard/firmware.git,$(COLDCARD_REV))
	cd $(COLDCARD) && git submodule update --init external/micropython external/libngu external/mpy-qr external/ckcc-protocol
	$(MAKE) -C $(COLDCARD)/external/micropython/mpy-cross CFLAGS_EXTRA="$(COLDCARD_CFLAGS)"
	cd $(COLDCARD)/unix && $(MAKE) setup CFLAGS_EXTRA="$(COLDCARD_CFLAGS)" && $(MAKE) ngu-setup && $(MAKE) CFLAGS_EXTRA="$(COLDCARD_CFLAGS)"
	uv venv -q -p 3.12 build/venv-coldcard
	uv pip install -q -p build/venv-coldcard/bin/python pysdl2 pillow hidapi ecdsa pyaes
	$(call clone,$(BITCOINJS),https://github.com/bitcoinjs/bitcoinjs-lib.git,$(BITCOINJS_REV))
	cd $(BITCOINJS) && npm ci --ignore-scripts --no-audit --no-fund
	uv venv -q -p 3.12 build/venv-wally
	uv pip install -q -p build/venv-wally/bin/python --require-hashes -r adapters/requirements-wally.txt
.PHONY: deps

build/rust-bitcoin-review: adapters/rust-bitcoin/src/main.rs adapters/rust-bitcoin/Cargo.lock
	mkdir -p build
	cargo build --release --locked --manifest-path adapters/rust-bitcoin/Cargo.toml
	cp adapters/rust-bitcoin/target/release/rust-bitcoin-review $@

build/coconut-review: adapters/coconut/bin/review.dart adapters/coconut/pubspec.lock
	mkdir -p build
	cd adapters/coconut && dart pub get --enforce-lockfile
	dart compile exe adapters/coconut/bin/review.dart -o $@

# The comparison's cases as one file, for a signer's own tests (README.md)
build/vectors.json: $(MODEL) adapters/vectors.mjs adapters/compare.mjs | seeds
	mkdir -p build
	node adapters/vectors.mjs 5 1 > $@
vectors: build/vectors.json
.PHONY: vectors

# Exact agreement where a signer's review reports the model's decisions, the invariants otherwise (README.md)
check-bitwasm: $(MODEL)
	node adapters/bitwasm.mjs 300 1
check-seedsigner: $(MODEL)
	node adapters/seedsigner.mjs 100 1
check-krux: $(MODEL)
	node adapters/krux.mjs 100 1
check-specter: $(MODEL)
	node adapters/specter.mjs 100 1
# Runs Coldcard's simulator headless, which needs SDL2 (brew install sdl2)
check-coldcard: $(MODEL)
	node adapters/coldcard.mjs 100 1
check-coconut: $(MODEL) build/coconut-review
	node adapters/coconut.mjs 100 1
check-bitcoinjs: $(MODEL)
	node adapters/bitcoinjs.mjs 100 1
# Needs bitcoind on PATH (or BITCOIND); it runs on regtest in a temporary datadir
check-core: $(MODEL)
	node adapters/core.mjs 100 1
	node adapters/core-rules.mjs
check-wally: $(MODEL)
	node adapters/wally.mjs 100 1
check-rust-bitcoin: $(MODEL) build/rust-bitcoin-review
	node adapters/rust-bitcoin.mjs 100 1
.PHONY: check-bitwasm check-seedsigner check-krux check-specter check-coldcard check-coconut check-bitcoinjs check-core check-wally check-rust-bitcoin
