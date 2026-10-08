use core::fmt::Write;

use frost_rerandomized::RandomizedCiphersuite;
use reddsa_frost::redjubjub::{Field, Group};

fn vectors<C: RandomizedCiphersuite>(output: &mut String) {
    writeln!(output, "{}", C::ID).unwrap();
    writeln!(
        output,
        "{}",
        hex::encode(C::Group::serialize(&C::Group::generator()).unwrap())
    )
    .unwrap();

    let messages = [
        Vec::new(),
        b"Zakura FROST ciphersuite extraction".to_vec(),
        (0u8..=255).collect(),
    ];
    for message in messages {
        for scalar in [
            C::H1(&message),
            C::H2(&message),
            C::H3(&message),
            C::HDKG(&message).unwrap(),
            C::HID(&message).unwrap(),
            C::hash_randomizer(&message).unwrap(),
        ] {
            writeln!(
                output,
                "{}",
                hex::encode(<C::Group as Group>::Field::serialize(&scalar))
            )
            .unwrap();
        }
        writeln!(output, "{}", hex::encode(C::H4(&message))).unwrap();
        writeln!(output, "{}", hex::encode(C::H5(&message))).unwrap();
    }
}

#[test]
fn ciphersuites_match_before_extraction() {
    // Captured from Common commit 64e30c21c1ba5aa0742c9a48f31d80e0dcdaa41f,
    // using the same public ciphersuite calls through `reddsa::frost`.
    let mut output = String::new();
    vectors::<reddsa_frost::redjubjub::JubjubBlake2b512>(&mut output);
    vectors::<reddsa_frost::redpallas::PallasBlake2b512>(&mut output);
    assert_eq!(output, include_str!("fixtures/ciphersuites.txt"));
}
