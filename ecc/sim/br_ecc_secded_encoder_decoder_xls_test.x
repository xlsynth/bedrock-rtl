// Copyright 2024-2025 The Bedrock-RTL Authors
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

// These tests were originally copied from https://github.com/xlsynth/dslx-llm/blob/main/samples/ecc.md.

import ecc.rtl.br_ecc_secded_encoder_xls as enc;
import ecc.rtl.br_ecc_secded_decoder_xls as dec;

// TODO(mgottscho): generalize K to data width not just message width

// Tests the encoder and decoder without any injected errors.
fn no_errors<N: u32, K: u32>(data: bits[K]) -> bool {
    const R: u32 = N - K;
    let (enc_data, enc_parity, _enc_codeword) = enc::br_ecc_secded_encoder_xls<K, R, N>(data);
    let (_dec_codeword, ce, due, syndrome, dec_data) = dec::br_ecc_secded_decoder_xls<K, R, N>(enc_data, enc_parity);
    !ce && !due && syndrome == uN[R]:0 && data == dec_data
}

// Tests that all single-bit errors are corrected.
fn single_bit_error_corrected<N: u32, K: u32>(data: bits[K], pos: u32) -> bool {
    const R: u32 = N - K;
    let (_enc_data, _enc_parity, enc_codeword) = enc::br_ecc_secded_encoder_xls<K, R, N>(data);
    if pos < N {
        let rcv_codeword = bit_slice_update(enc_codeword, pos, (!enc_codeword[pos +: u1]) as u1);
        let rcv_data = rcv_codeword[0 +: uN[K]];
        let rcv_parity = rcv_codeword[K +: uN[R]];
        let (_dec_codeword, ce, due, syndrome, dec_data) = dec::br_ecc_secded_decoder_xls<K, R, N>(rcv_data, rcv_parity);
        ce && !due && syndrome != uN[R]:0 && data == dec_data
    } else {
        true
    }
}

// Tests that all double-bit errors are detected.
fn double_bit_error_detected<N: u32, K: u32>(data: bits[K], pos0: u32, pos1: u32) -> bool {
    const R: u32 = N - K;
    let (_enc_data, _enc_parity, enc_codeword) = enc::br_ecc_secded_encoder_xls<K, R, N>(data);
    if pos0 < N && pos1 < N && pos0 < pos1 {
        let flipped0 = bit_slice_update(enc_codeword, pos0, (!enc_codeword[pos0 +: u1]) as u1);
        let rcv_codeword = bit_slice_update(flipped0, pos1, (!flipped0[pos1 +: u1]) as u1);
        let rcv_data = rcv_codeword[0 +: uN[K]];
        let rcv_parity = rcv_codeword[K +: uN[R]];
        let (_dec_codeword, ce, due, syndrome, _dec_data) = dec::br_ecc_secded_decoder_xls<K, R, N>(rcv_data, rcv_parity);
        !ce && due && syndrome != uN[R]:0
    } else {
        true
    }
}

// Tests that all triple-bit errors are detected. They may sometimes be corrected or miscorrected, but
// must not be silently undetected.
fn triple_bit_error_not_undetected<N: u32, K: u32>(data: bits[K], pos0: u32, pos1: u32, pos2: u32) -> bool {
    const R: u32 = N - K;
    let (_enc_data, _enc_parity, enc_codeword) = enc::br_ecc_secded_encoder_xls<K, R, N>(data);
    if pos0 < N && pos1 < N && pos0 < pos1 {
        let flipped0 = bit_slice_update(enc_codeword, pos0, (!enc_codeword[pos0 +: u1]) as u1);
        let flipped1 = bit_slice_update(flipped0, pos1, (!flipped0[pos1 +: u1]) as u1);
        let rcv_codeword = bit_slice_update(flipped1, pos2, (!flipped1[pos2 +: u1]) as u1);
        let rcv_data = rcv_codeword[0 +: uN[K]];
        let rcv_parity = rcv_codeword[K +: uN[R]];
        let (_dec_codeword, ce, due, syndrome, _dec_data) = dec::br_ecc_secded_decoder_xls<K, R, N>(rcv_data, rcv_parity);
        (ce || due) && syndrome != uN[R]:0
        // Cannot check that if CE the dec_data matches the data because a miscorrection is possible.
    } else {
        true
    }
}

// Tests that the code is in systematic form (first K bits of the encoded codeword match the message).
fn systematic<N: u32, K: u32>(data: bits[K]) -> bool {
    const R: u32 = N - K;
    let (_enc_data, _enc_parity, enc_codeword) = enc::br_ecc_secded_encoder_xls<K, R, N>(data);
    data == enc_codeword[0 +: uN[K]]
}


// No error injection
#[quickcheck(exhaustive)]
fn quickcheck_no_errors_n8_k4(message: bits[4]) -> bool {
    no_errors<u32:8, u32:4>(message)
}
#[quickcheck(exhaustive)]
fn quickcheck_no_errors_n13_k8(message: bits[8]) -> bool {
    no_errors<u32:13, u32:8>(message)
}
#[quickcheck(exhaustive)]
fn quickcheck_no_errors_n16_k11(message: bits[11]) -> bool {
    no_errors<u32:16, u32:11>(message)
}
#[quickcheck(exhaustive)]
fn quickcheck_no_errors_n22_k16(message: bits[16]) -> bool {
    no_errors<u32:22, u32:16>(message)
}
#[quickcheck(exhaustive)]
fn quickcheck_no_errors_n32_k26(message: bits[26]) -> bool {
    no_errors<u32:32, u32:26>(message)
}
#[quickcheck(exhaustive)]
fn quickcheck_no_errors_n39_k32(message: bits[32]) -> bool {
    no_errors<u32:39, u32:32>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n64_k57(message: bits[57]) -> bool {
    no_errors<u32:64, u32:57>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n72_k64(message: bits[64]) -> bool {
    no_errors<u32:72, u32:64>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n128_k120(message: bits[120]) -> bool {
    no_errors<u32:128, u32:120>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n137_k128(message: bits[128]) -> bool {
    no_errors<u32:137, u32:128>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n256_k247(message: bits[247]) -> bool {
    no_errors<u32:256, u32:247>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n266_k256(message: bits[256]) -> bool {
    no_errors<u32:266, u32:256>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n512_k502(message: bits[502]) -> bool {
    no_errors<u32:512, u32:502>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n523_k512(message: bits[512]) -> bool {
    no_errors<u32:523, u32:512>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n1024_k1013(message: bits[1013]) -> bool {
    no_errors<u32:1024, u32:1013>(message)
}
#[quickcheck(test_count=100)]
fn quickcheck_no_errors_n1036_k1024(message: bits[1024]) -> bool {
    no_errors<u32:1036, u32:1024>(message)
}


// Single bit error injection
#[quickcheck(exhaustive)]
fn quickcheck_single_bit_error_corrected_n8_k4(message: bits[4], pos: u32) -> bool {
    single_bit_error_corrected<u32:8, u32:4>(message, pos)
}
#[quickcheck(exhaustive)]
fn quickcheck_single_bit_error_corrected_n13_k8(message: bits[8], pos: u32) -> bool {
    single_bit_error_corrected<u32:13, u32:8>(message, pos)
}
#[quickcheck(exhaustive)]
fn quickcheck_single_bit_error_corrected_n16_k11(message: bits[11], pos: u32) -> bool {
    single_bit_error_corrected<u32:16, u32:11>(message, pos)
}
#[quickcheck(exhaustive)]
fn quickcheck_single_bit_error_corrected_n22_k16(message: bits[16], pos: u32) -> bool {
    single_bit_error_corrected<u32:22, u32:16>(message, pos)
}
#[quickcheck(exhaustive)]
fn quickcheck_single_bit_error_corrected_n32_k26(message: bits[26], pos: u32) -> bool {
    single_bit_error_corrected<u32:32, u32:26>(message, pos)
}
#[quickcheck(exhaustive)]
fn quickcheck_single_bit_error_corrected_n39_k32(message: bits[32], pos: u32) -> bool {
    single_bit_error_corrected<u32:39, u32:32>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n64_k57(message: bits[57], pos: u32) -> bool {
    single_bit_error_corrected<u32:64, u32:57>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n72_k64(message: bits[64], pos: u32) -> bool {
    single_bit_error_corrected<u32:72, u32:64>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n128_k120(message: bits[120], pos: u32) -> bool {
    single_bit_error_corrected<u32:128, u32:120>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n137_k128(message: bits[128], pos: u32) -> bool {
    single_bit_error_corrected<u32:137, u32:128>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n256_k247(message: bits[247], pos: u32) -> bool {
    single_bit_error_corrected<u32:256, u32:247>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n266_k256(message: bits[256], pos: u32) -> bool {
    single_bit_error_corrected<u32:266, u32:256>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n512_k502(message: bits[502], pos: u32) -> bool {
    single_bit_error_corrected<u32:512, u32:502>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n523_k512(message: bits[512], pos: u32) -> bool {
    single_bit_error_corrected<u32:523, u32:512>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n1024_k1013(message: bits[1013], pos: u32) -> bool {
    single_bit_error_corrected<u32:1024, u32:1013>(message, pos)
}
#[quickcheck(test_count=100)]
fn quickcheck_single_bit_error_corrected_n1036_k1024(message: bits[1024], pos: u32) -> bool {
    single_bit_error_corrected<u32:1036, u32:1024>(message, pos)
}


// Double bit error injection
#[quickcheck(exhaustive)]
fn quickcheck_double_bit_error_detected_n8_k4(message: bits[4], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:8, u32:4>(message, pos0, pos1)
}
#[quickcheck(exhaustive)]
fn quickcheck_double_bit_error_detected_n13_k8(message: bits[8], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:13, u32:8>(message, pos0, pos1)
}
#[quickcheck(exhaustive)]
fn quickcheck_double_bit_error_detected_n16_k11(message: bits[11], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:16, u32:11>(message, pos0, pos1)
}
#[quickcheck(exhaustive)]
fn quickcheck_double_bit_error_detected_n22_k16(message: bits[16], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:22, u32:16>(message, pos0, pos1)
}
#[quickcheck(exhaustive)]
fn quickcheck_double_bit_error_detected_n32_k26(message: bits[26], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:32, u32:26>(message, pos0, pos1)
}
#[quickcheck(exhaustive)]
fn quickcheck_double_bit_error_detected_n39_k32(message: bits[32], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:39, u32:32>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n64_k57(message: bits[57], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:64, u32:57>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n72_k64(message: bits[64], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:72, u32:64>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n128_k120(message: bits[120], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:128, u32:120>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n137_k128(message: bits[128], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:137, u32:128>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n256_k247(message: bits[247], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:256, u32:247>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n266_k256(message: bits[256], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:266, u32:256>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n512_k502(message: bits[502], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:512, u32:502>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n523_k512(message: bits[512], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:523, u32:512>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n1024_k1013(message: bits[1013], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:1024, u32:1013>(message, pos0, pos1)
}
#[quickcheck(test_count=100)]
fn quickcheck_double_bit_error_detected_n1036_k1024(message: bits[1024], pos0: u32, pos1: u32) -> bool {
    double_bit_error_detected<u32:1036, u32:1024>(message, pos0, pos1)
}


// Triple bit error injection
#[quickcheck(exhaustive)]
fn quickcheck_triple_bit_error_not_undetected_n8_k4(message: bits[4], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:8, u32:4>(message, pos0, pos1, pos2)
}
#[quickcheck(exhaustive)]
fn quickcheck_triple_bit_error_not_undetected_n13_k8(message: bits[8], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:13, u32:8>(message, pos0, pos1, pos2)
}
#[quickcheck(exhaustive)]
fn quickcheck_triple_bit_error_not_undetected_n16_k11(message: bits[11], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:16, u32:11>(message, pos0, pos1, pos2)
}
#[quickcheck(exhaustive)]
fn quickcheck_triple_bit_error_not_undetected_n22_k16(message: bits[16], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:22, u32:16>(message, pos0, pos1, pos2)
}
#[quickcheck(exhaustive)]
fn quickcheck_triple_bit_error_not_undetected_n32_k26(message: bits[26], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:32, u32:26>(message, pos0, pos1, pos2)
}
#[quickcheck(exhaustive)]
fn quickcheck_triple_bit_error_not_undetected_n39_k32(message: bits[32], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:39, u32:32>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n64_k57(message: bits[57], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:64, u32:57>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n72_k64(message: bits[64], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:72, u32:64>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n128_k120(message: bits[120], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:128, u32:120>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n137_k128(message: bits[128], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:137, u32:128>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n256_k247(message: bits[247], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:256, u32:247>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n266_k256(message: bits[256], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:266, u32:256>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n512_k502(message: bits[502], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:512, u32:502>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n523_k512(message: bits[512], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:523, u32:512>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n1024_k1013(message: bits[1013], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:1024, u32:1013>(message, pos0, pos1, pos2)
}
#[quickcheck(test_count=100)]
fn quickcheck_triple_bit_error_not_undetected_n1036_k1024(message: bits[1024], pos0: u32, pos1: u32, pos2: u32) -> bool {
    triple_bit_error_not_undetected<u32:1036, u32:1024>(message, pos0, pos1, pos2)
}
