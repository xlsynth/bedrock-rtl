# Copyright 2024 The Bedrock-RTL Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""
Hsiao SECDED code generator

References:
[1] https://ieeexplore.ieee.org/abstract/document/5391627
[2] https://arxiv.org/pdf/0803.1217

"""

import numpy as np
import math
import argparse


def num_parity_bits(message_bits: int) -> int:
    """Calculate the number of parity bits required for a Hsiao SECDED code with the given message length in bits."""
    r = 1
    while r < math.ceil(math.log2(message_bits + r)) + 1:
        r += 1
    return r


def num_codeword_bits(message_bits: int, parity_bits: int) -> int:
    """Calculate the total number of bits in a codeword for a Hsiao SECDED code with the given message length and parity length in bits."""
    return message_bits + parity_bits


def num_message_bits(codeword_bits: int, parity_bits: int) -> int:
    """Calculate the number of message bits in a codeword for a Hsiao SECDED code with the given codeword length and parity length in bits."""
    return codeword_bits - parity_bits


def uint_to_bit_vector(number: int, bit_length: int) -> list:
    """Convert an unsigned integer to a vector of bits with a specified length."""
    if number < 0:
        raise ValueError("Number must be non-negative.")
    binary_str = format(number, f"0{bit_length}b")
    bit_vector = [int(bit) for bit in binary_str]
    return bit_vector


def min_column_weight(message_bits: int, parity_bits: int) -> int:
    """Returns the smallest odd column weight that can be used to construct the parity-check matrix."""
    codeword_bits = num_codeword_bits(message_bits, parity_bits)
    for i in range(1, 2**parity_bits, 2):
        bitvec = uint_to_bit_vector(i, parity_bits)
        weight = sum(bitvec)
        if weight % 2 == 1:
            num_ways = math.comb(parity_bits, weight)
            if num_ways >= message_bits:
                return weight
    raise ValueError("No valid column weight found!")


def parity_check_message_columns(
    parity_bits: int, message_bits: int, col_weight: int
) -> np.ndarray:
    """Returns all possible values for a parity column with the given weight."""
    # This is not the most efficient way of finding the columns, but it works!
    ret = np.zeros((parity_bits, message_bits), dtype=int)
    i = 0
    c = 0
    while c < message_bits:
        vec = uint_to_bit_vector(i, parity_bits)
        if sum(vec) == col_weight:
            assert (sum(vec) % 2) == 1
            ret[:, c] = vec
            c += 1
        i += 1
    assert check_columns_unique(ret)
    return ret


def check_columns_unique(matrix: np.ndarray) -> bool:
    """Check that no columns are the same in the given matrix."""
    for ci in range(matrix.shape[1]):
        for cj in range(ci + 1, matrix.shape[1]):
            assert not np.array_equal(matrix[:, ci], matrix[:, cj])
    return True


def parity_check_matrix(message_bits: int, parity_bits: int) -> np.ndarray:
    """Generate the n x r parity-check matrix for a Hsiao SECDED code with the given number of parity bits.

    Reference [2] states:
    > The definition of Hsiao code is a type of SEC-DED codes whose check matrix H defined on GF(2)
    > satisfies:
    > (1) Every column contains an odd number of 1s.
    > (2) The total number of 1s reaches the minimum.
    > (3) The difference of the number of 1s in any two rows is not greater than 1.
    > (4) No two columns are the same.
    """
    k = message_bits
    r = parity_bits
    n = num_codeword_bits(k, r)
    # Fill H_m with column vectors that satisfy conditions (1), (2), and (4).
    min_msg_col_weight = min_column_weight(k, r)
    print(f"Minimum message column weight: {min_msg_col_weight}")
    H_m = parity_check_message_columns(r, k, min_msg_col_weight)
    # r x r matrix for parity bits (identity)
    H_p = np.identity(r, dtype=int)
    return np.hstack((H_m, H_p))  # Combine data and parity


def generator_matrix(parity_check_matrix: np.ndarray) -> np.ndarray:
    """Generate the generator matrix for a Hsiao SECDED code with the given parity-check matrix."""
    # G = [I_k | P], where P = transpose of H_d
    r = parity_check_matrix.shape[0]
    n = parity_check_matrix.shape[1]
    k = num_message_bits(n, r)
    # TODO(mgottscho): Implement this
    return np.zeros((k, n), dtype=int)


def hsiao_secded_code(message_bits: int) -> tuple[int, int, np.ndarray, np.ndarray]:
    """Generate a Hsiao SECDED code with the given number of message bits.

    Args:
        message_bits: Number of message bits (k)

    Returns:
        tuple[int, int, np.ndarray, np.ndarray]:
            - Number of parity bits (r)
            - Number of codeword bits (n)
            - Parity-check matrix (H) of shape r x n
            - Generator matrix (G) of shape k x n
        Such that c = m * G and s = H * c^T, where:
            - m is the 1 x k message
            - c is the 1 x n codeword
            - s is the r x 1 syndrome
    """
    k = message_bits
    r = num_parity_bits(k)
    n = num_codeword_bits(k, r)
    print(f"Number of message bits (k): {k}")
    print(f"Number of parity bits (r): {r}")
    print(f"Number of codeword bits (n): {n}")
    print("Constructing parity-check matrix H.")
    H = parity_check_matrix(k, r)
    print("Constructing generator matrix G.")
    G = generator_matrix(H)
    print("Parity-Check Matrix H:")
    print(H)
    print("Generator Matrix G:")
    print(G)
    return r, n, H, G


def main():
    parser = argparse.ArgumentParser(description="Hsiao SECDED code generator.")
    parser.add_argument("k", type=int, help="Number of data bits (k)")
    args = parser.parse_args()
    hsiao_secded_code(args.k)


if __name__ == "__main__":
    main()
