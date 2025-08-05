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

import ecc.rtl.br_ecc_secded_encoder_xls as enc;
import ecc.rtl.br_ecc_secded_decoder_xls as dec;

// Instance parameters for the (72,64) SECDED code.
const K = u32:64;
const R = u32:8;
const N = K + R;

// Tests the encoder and decoder without any injected errors.
#[quickcheck(test_count=1000000)]
fn quickcheck_no_errors(message: bits[K]) -> bool {
    let codeword = enc::br_ecc_secded_encoder_xls(message);
    let (decoded_message, ce, due) = dec::br_ecc_secded_decoder_xls(codeword);
    !ce && !due && message == decoded_message
}

// Tests that all single-bit errors are corrected.
#[quickcheck(test_count=1000000)]
fn quickcheck_single_bit_error_correction(message: bits[K], pos: u32) -> bool {
    let codeword = enc::br_ecc_secded_encoder_xls(message);
    if pos < N {
        let received_codeword = bit_slice_update(codeword, pos, (!codeword[pos +: u1]) as u1);
        let (decoded_message, ce, due) = dec::br_ecc_secded_decoder_xls(received_codeword);
        ce && !due && decoded_message == message
    } else {
        true
    }
}

// Tests that all double-bit errors are detected.
#[quickcheck(test_count=1000000)]
fn quickcheck_double_bit_error_detection(message: bits[K], pos0: u32, pos1: u32) -> bool {
    let codeword = enc::br_ecc_secded_encoder_xls(message);
    if pos0 < N && pos1 < N && pos0 < pos1 {
        let flipped0 = bit_slice_update(codeword, pos0, (!codeword[pos0 +: u1]) as u1);
        let received_codeword = bit_slice_update(flipped0, pos1, (!flipped0[pos1 +: u1]) as u1);
        let (_, ce, due) = dec::br_ecc_secded_decoder_xls(received_codeword);
        !ce && due
    } else {
        true
    }
}

// Tests that all triple-bit errors are detected. They may sometimes be corrected or miscorrected, but
// must not be silently undetected.
#[quickcheck(test_count=1000000)]
fn quickcheck_triple_bit_error_not_undetected(message: bits[K], pos0: u32, pos1: u32, pos2: u32) -> bool {
    let codeword = enc::br_ecc_secded_encoder_xls(message);
    if pos0 < N && pos1 < N && pos2 < N && pos0 < pos1 && pos1 < pos2 {
        let flipped0 = bit_slice_update(codeword, pos0, (!codeword[pos0 +: u1]) as u1);
        let flipped1 = bit_slice_update(flipped0, pos1, (!flipped0[pos1 +: u1]) as u1);
        let received_codeword = bit_slice_update(flipped1, pos2, (!flipped1[pos2 +: u1]) as u1);
        let (_, ce, due) = dec::br_ecc_secded_decoder_xls(received_codeword);
        ce || due
    } else {
        true
    }
}

// Tests that the code is in systematic form (first K bits of the encoded codeword match the message).
#[quickcheck(test_count=1000000)]
fn quickcheck_systematic(message: bits[K]) -> bool {
    let codeword = enc::br_ecc_secded_encoder_xls(message);
    message == codeword[0 +: uN[K]]
}
