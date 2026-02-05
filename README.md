Privacy-preserving age proofs using incrementally verifiable computation for Aadhaar QR codes retrofitted with Falcon signatures.
------
<a href="https://falcon-sign.info/falcon.pdf" target="_blank">Falcon signature</a> is a lattice based signature, and a winner of [NIST PQC competition](https://csrc.nist.gov/Projects/post-quantum-cryptography/selected-algorithms-2022). It has desirable properties such as compact signatures and relatively simple verification.

<a href="https://falcon-sign.info/falcon.pdf" target="_blank">Bellpepper</a> is a Rust library that we use to generate R1CS circuits which are used to create zero-knowledge proofs that attest to a prover knowing a valid Aadhaar QR code with a Falcon signature.

We design and implement Falcon signature verification as an incremental computation and combine it with Nova Aadhaar's implementation in Bellpepper for creating privacy-preserving age proofs.

## Project Structure

- [`core/`](core/) - Main Falcon Aadhaar implementation
- [`dependencies/falcon-rust/`](dependencies/falcon-rust/) - Rust wrapper for Falcon signatures,
  sourced from <a href="https://github.com/zhenfeizhang/falcon.rs/tree/master/falcon-rust" target="_blank">zhenfeizhang/falcon.rs/falcon-rust</a>.
- [`dependencies/falcon-r1cs/`](dependencies/falcon-r1cs/) - R1CS circuits for Falcon signature verification using Arkworks framework,
  sourced from <a href="https://github.com/zhenfeizhang/falcon.rs/tree/master/falcon-r1cs" target="_blank">zhenfeizhang/falcon.rs/falcon-r1cs</a>.
- [`dependencies/nova-aadhaar-qr/`](dependencies/nova-aadhaar-qr/) - Implementation of
  <a href="https://www.ee.iitb.ac.in/~sarva/zk/aadhaar-age-proof.pdf" target="_blank">Nova Aadhaar</a>,
  sourced from <a href="https://github.com/avras/nova-aadhaar-qr" target="_blank">avras/nova-aadhaar-qr</a>.