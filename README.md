Privacy-Preserving Age Proofs for Aadhaar Using Falcon
------
We retrofit Aadhaar QR codes with post-quantum <a href="https://falcon-sign.info/falcon.pdf" target="_blank">Falcon signatures</a> and construct a privacy-preserving age proof using incrementally verifiable computation (IVC). Our primary contributions include Falcon verification as an incremental computation, compatible with standard implementations and creating privacy-preserving age proofs on Aadhaar QR codes using Falcon signatues. We haved developed R1CS circuits using Bellpepper for Falcon signature proof of possession (PoP) and age threshold checks on Aadhaar QR data with Falcon signatures in place of RSA signatures and combined them with <a href="https://eprint.iacr.org/2021/370.pdf" target="_blank">Nova</a> folding for efficient proof generation.

> [!WARNING]
> This code has not been audited. Use with care.


## What Is Inside an Aadhaar QR Code?
An Aadhaar QR code encodes digitally signed information about an Aadhaar holder. It is printed on the back of the physical Aadhaar card and can also be obtained through the mAadhaar app (<a href="https://play.google.com/store/apps/details?id=in.gov.uidai.mAadhaarPlus" target="_blank">Google Play</a>, <a href="https://apps.apple.com/in/app/maadhaar/id1435469474" target="_blank">App Store</a>). The QR payload includes the following details about the holder.

- Last 4 digits of Aadhaar number
- Name
- Date of birth
- Gender
- Address fields
- Last 4 digits of mobile number
- Photo (binary image data)
- Signature by UIDAI on the QR payload (RSA)

In this project, we replace the classical (RSA) signature with the post-quantum secure Falcon signature scheme and construct Falcon-signed versions of the Aadhaar QR code. We use the <a href="https://eprint.iacr.org/2021/370.pdf" target="_blank">Nova</a> folding scheme to produce privacy-preserving age proofs on the Falcon-signed Aadhaar QR code.

## Running the Examples

### 1) Generate or Validate UIDAI Falcon Key Pair Generation

This creates `keys/uidai_falcon_sk.bin` and `keys/uidai_falcon_pk.bin` if they are missing, or validates existing key pair.

```
$ cargo run --release --example generate_uidai_keys
    Finished `release` profile [optimized] target(s) in 1.30s
     Running `<project_root>/target/release/examples/generate_uidai_keys`
Generated UIDAI Falcon key key pair
Secret key: <project_root>/keys/uidai_falcon_sk.bin (1281 bytes)
Public key: <project_root>/keys/uidai_falcon_pk.bin (897 bytes)
Falcon signature length for this build: 666 bytes
Key pair generation time: 11.48ms
Total runtime: 12.34ms
```

### 2) Generate a Falcon-Signed Aadhaar QR PNG

You will need a legacy Aadhaar QR image downloaded from mAadhaar to run this example. The output is a QR PNG that contains the Falcon signature using the generated keys in place of the RSA signature.

```
$ cargo run --release --example generate_falcon_qr aadhaar_qr.png falcon_qr.png
    Finished `release` profile [optimized] target(s) in 9.60s
     Running `<project_root>/target/release/examples/generate_falcon_qr aadhaar_qr.png falcon_qr.png`
Falcon signature verification PASSED!
Generated Falcon-signed Aadhaar QR PNG: falcon_qr.png
Payload bytes: 1123, signature bytes: 666, total bytes: 1789
QR generation time: 53.25ms
Total runtime: 53.69ms
```

### 3) Create an Age Proof on Falcon QR

Provide Aadhaar QR with Falcon signature image file and current date in `DD-MM-YYYY` format.

```
$ cargo run --release --example age_proof falcon_qr.png 23-04-2026
    Finished `release` profile [optimized] target(s) in 0.52s
     Running `<project_root>/target/release/examples/age_proof falcon_qr.png 23-04-2026`
Number of bytes in QR code: 1789
Producing public parameters...
PublicParams::setup, took 3.119356959s 
Number of constraints per step (primary circuit): 244344
Number of constraints per step (secondary circuit): 10349
Number of variables per step (primary circuit): 244366
Number of variables per step (secondary circuit): 10331
Number of SHAKE256.inject steps: 9
Number of steps: 9
Generating a RecursiveSNARK...
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 0: true, took 208ns
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 1: true, took 499.862917ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 2: true, took 538.898625ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 3: true, took 543.906042ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 4: true, took 554.400708ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 5: true, took 563.501125ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 6: true, took 577.476875ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 7: true, took 585.231542ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 8: true, took 583.465125ms
Total time taken by RecursiveSNARK::prove_steps: 4.446823417s
Verifying a RecursiveSNARK...
RecursiveSNARK::verify: true, took 314.761208ms
Generating a CompressedSNARK using Spartan with IPA-PC...
CompressedSNARK::prove: true, took 10.361119792s
Total proving time is 16.103760833s
CompressedSNARK::len 11205 bytes
Verifying a CompressedSNARK...
CompressedSNARK::verify: true, took 330.434917ms
=========================================================
Number of constraints per step: 244344
Public parameters generation time: 3.119356959s 
Total proving time (excl pp generation): 16.103760833s
Compressed SNARK size: 11.2 KB
Total verification time: 330.434917ms
=========================================================
Nullifier = 0x3c36427f6baf8d02571046e12f296400376b263d8d70d110292e394812fe21a4
```
the generated age proof will be stored in `compressed_snark.json`

### 4) Run Incremental Proof of Possession (Naive)

This runs the naive incremental proof-of-possession pipeline over a sample message/signature.

```
$ cargo run --release --example proof_possession_naive
    Finished `release` profile [optimized] target(s) in 15.32s
     Running `<project_root>/target/release/examples/proof_possession_naive`
Producing public parameters...
PublicParams::setup, took 1.935920083s 
Number of constraints per step (primary circuit): 55964
Number of constraints per step (secondary circuit): 10349
Number of variables per step (primary circuit): 56406
Number of variables per step (secondary circuit): 10331
Generating a RecursiveSNARK...
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 0: true, took 250ns
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 1: true, took 275.966875ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 2: true, took 287.968791ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
...
RecursiveSNARK::prove_step 510: true, took 278.683833ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 511: true, took 280.614125ms
Total time taken by RecursiveSNARK::prove_steps: 144.613657583s
Verifying a RecursiveSNARK...
RecursiveSNARK::verify: true, took 89.254667ms
Generating a CompressedSNARK using Spartan with IPA-PC...
CompressedSNARK::prove: true, took 2.999120208s
Total proving time is 148.267288042s
CompressedSNARK::len 10638 bytes
Verifying a CompressedSNARK...
CompressedSNARK::verify: true, took 103.448042ms
=========================================================
Number of constraints per step: 55964
Public parameters generation time: 1.861933125s 
Total proving time (excl pp generation): 148.267288042s
Compressed SNARK size: 10.6 KB
Total verification time: 103.448042ms
=========================================================
l2norm(s1,s2) = 0x0000000000000000000000000000000000000000000000000000000001c0c2ab
```

### 5) Run Incremental Proof of Possession (Aggregated)

This runs the aggregated incremental proof-of-possession pipeline and writes the proof into a `proof_possession.json`.

```
$ cargo run --release --example proof_possession_aggregated
    Finished `release` profile [optimized] target(s) in 14.19s
     Running `<project_root>/target/release/examples/proof_possession_aggregated`
Producing public parameters...
PublicParams::setup, took 2.069018375s 
Number of constraints per step (primary circuit): 68608
Number of constraints per step (secondary circuit): 10349
Number of variables per step (primary circuit): 68861
Number of variables per step (secondary circuit): 10331
Generating a RecursiveSNARK...
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 0: true, took 42ns
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 1: true, took 268.816541ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 2: true, took 277.350875ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 3: true, took 278.822583ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 4: true, took 280.58975ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 5: true, took 279.406167ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 6: true, took 278.862917ms
R1CSWitness::new succeeded
R1CSInstance::new succeeded
R1CSWitness::new succeeded
R1CSInstance::new succeeded
RecursiveSNARK::prove_step 7: true, took 286.012084ms
Total time taken by RecursiveSNARK::prove_steps: 1.949899167s
Verifying a RecursiveSNARK...
RecursiveSNARK::verify: true, took 110.6945ms
Generating a CompressedSNARK using Spartan with IPA-PC...
CompressedSNARK::prove: true, took 5.351118708s
Total proving time is 7.981971625s
Saved JSON proof to proof_possession.json
CompressedSNARK::len 10932 bytes
Verifying a CompressedSNARK...
CompressedSNARK::verify: true, took 184.010083ms
=========================================================
Number of constraints per step: 68608
Public parameters generation time: 2.069018375s 
Total proving time (excl pp generation): 7.981971625s
Compressed SNARK size: 10.9 KB
Total verification time: 184.010083ms
=========================================================
l2norm(s1,s2) = 0x0000000000000000000000000000000000000000000000000000000001bd11e4
```


Performance report:

| IVC | R1CS | PP Gen | Proof Gen | Proof Ver | CS Size | Fold Steps |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Age Proof | 244,344 | 3.063633333s | 16.047927792s | 380.183708ms | 11.2 KB | max(ceil((n - 666) / 136), 8) |
| Aggregated Proof of Possession | 268,608 | 2.140314792s | 8.181745334s | 184.770375ms | 10.9 KB | 8 |
| Naive Proof of Possession | 55,964 | 1.935920083s | 149.359159083s | 104.030833ms | 10.6 KB | 512 |

Legend: R1CS = R1CS Constraints per Step, PP Gen = Public Parameter Generation Time, Proof Gen = Proof Generation Time, Proof Ver = Proof Verification Time, CS Size = Compressed SNARK JSON File Size, Fold Steps = Number of recursive folding steps.
For Age Proof: n = total Falcon-signed QR payload length in bytes, and 666 bytes is the Falcon signature field; therefore n - 666 is the pre-signature payload length.

## Memory Consumption

To measure peak memory for the age proof run:

GNU time (Linux):

```
$ command time -v cargo run --release --example age_proof falcon_qr.png 23-04-2026
```

BSD time (macOS):

```
$ /usr/bin/time -l cargo run --release --example age_proof falcon_qr.png 23-04-2026
```

Peak memory usage report:

| IVC | Peak Memory (bytes) | Peak Memory (MB) |
| --- | ---: | ---: |
| Age Proof Using Falcon | 629804032 | 629.80 MB |
| Aggregated Proof of Possession | 286656640 | 286.66 MB |
| Naive Proof of Possession | 357550336 | 357.55 MB |

## Acknowledgement

This project is inspired by <a href="https://github.com/avras/nova-aadhaar-qr" target="_blank">Nova Aadhaar</a> by <a href="https://www.ee.iitb.ac.in/~sarva/" target="_blank">Prof Saravanan Vijayakumaran</a>, which first used Nova for privacy-preserving age proofs on RSA-signed Aadhaar QR codes.

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
