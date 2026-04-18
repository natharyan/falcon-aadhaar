Privacy-Preserving Age Proofs for Aadhaar Using Falcon
------
We retrofit Aadhaar QR codes with post-quantum <a href="https://falcon-sign.info/falcon.pdf" target="_blank">Falcon signature</a> and construct a privacy-preserving age proof using incrementally verifiable computation (IVC). Our primary contribution is Falcon verification as an incremental computation, compatible with standard implementations. We develop R1CS circuits using <a href="https://falcon-sign.info/falcon.pdf" target="_blank">Bellpepper</a> for Falcon signature verification and age threshold check on an Aadhaar QR code, combined with Nova folding for efficient zero-knowledge proofs. We compare our R1CS metrics with prior age proof work and Falcon proof of possession.

## Project Structure

- [`core/`](core/) - core implementation for age proof and Falcon signature proof of possession.
- [`dependencies/falcon-rust/`](dependencies/falcon-rust/) - Rust wrapper for Falcon signatures,
  sourced from <a href="https://github.com/zhenfeizhang/falcon.rs/tree/master/falcon-rust" target="_blank">zhenfeizhang/falcon.rs/falcon-rust</a>.
- [`dependencies/falcon-r1cs/`](dependencies/falcon-r1cs/) - R1CS circuits for Falcon signature verification using Arkworks framework, sourced from <a href="https://github.com/zhenfeizhang/falcon.rs/tree/master/falcon-r1cs" target="_blank">zhenfeizhang/falcon.rs/falcon-r1cs</a>.
- [`dependencies/nova-aadhaar-qr/`](dependencies/nova-aadhaar-qr/) - implementation of
  <a href="https://www.ee.iitb.ac.in/~sarva/zk/aadhaar-age-proof.pdf" target="_blank">Nova Aadhaar</a>,
  sourced from <a href="https://github.com/avras/nova-aadhaar-qr" target="_blank">avras/nova-aadhaar-qr</a>.
