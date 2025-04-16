# Copyright 2024-2025 The Bedrock-RTL Authors
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
import textwrap


def delta_matrix(R: int, J: int, m: int) -> np.ndarray:
    """
    Build the R x m recursively-balanced matrix ∆(R,J,m) as described in [2]:
    - All columns have weight J,
    - No two columns identical,
    - Row-sums differ by at most 1.
    """
    # Base cases
    if m == 0:
        return np.zeros((R, 0), dtype=int)
    if J == 0:
        return np.zeros((R, m), dtype=int)
    if J == R:
        return np.ones((R, m), dtype=int)
    if m == 1:
        col = np.zeros((R, 1), dtype=int)
        col[:J, 0] = 1
        return col
    if J == 1:
        M = np.zeros((R, m), dtype=int)
        for i in range(m):
            M[i, i] = 1
        return M
    if J == R - 1:
        M = np.ones((R, m), dtype=int)
        for i in range(m):
            M[i, i] = 0
        return M

    # Recursive split
    m1 = math.ceil(m * J / R)
    m2 = m - m1
    M1 = delta_matrix(R - 1, J - 1, m1)
    M2 = delta_matrix(R - 1, J, m2)

    # Compute extra‑1 rows in each part
    r1 = ((J - 1) * m1) % (R - 1)
    r2 = (J * m2) % (R - 1)

    # Rotate M2's rows to balance
    def _rotate_M2(M2: np.ndarray, r1: int, r2: int) -> np.ndarray:
        total = R - 1
        if r2 == 0:
            return M2
        if r1 + r2 > total:
            cut = r2 - (r1 + r2 - total)
            return np.vstack((M2[cut:], M2[:cut]))
        else:
            top = M2[:r2]
            rest = M2[r2:]
            return np.vstack((rest[:r1], top, rest[r1:]))

    M2p = _rotate_M2(M2, r1, r2)

    # Build the full block
    top_row = np.hstack((np.ones(m1, dtype=int), np.zeros(m2, dtype=int)))[None, :]
    bottom = np.hstack((M1, M2p))
    delta = np.vstack((top_row, bottom))

    # Check that the required properties of the delta matrix are satisfied
    check_columns_have_weight(delta, J)
    check_columns_unique(delta)
    check_row_sums_differ_by_at_most_one(delta)
    return delta


def horizontal_union(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """
    N ⊕ M: flip M upside-down, hstack it onto A, then
    reorder rows by descending row-sum to re-balance.
    """
    M_up = np.flipud(B)
    C = np.hstack((A, M_up))
    order = np.argsort(-C.sum(axis=1))
    return C[order]


def get_r(k: int) -> int:
    """Calculate the number of parity bits (p) required for a Hsiao SECDED code with the given message length (k) in bits."""
    r = 1
    while r < math.ceil(math.log2(k + r)) + 1:
        r += 1
    return r


def uint_to_bit_vector(number: int, bit_length: int) -> np.ndarray:
    """Convert an unsigned integer to a vector of bits with a specified length."""
    if number < 0:
        raise ValueError("Number must be non-negative.")
    binary_str = format(number, f"0{bit_length}b")
    return np.array([int(bit) for bit in binary_str])


def bit_vector_to_uint(bit_vector: np.ndarray) -> int:
    """Convert a bit vector to an unsigned integer."""
    return int("".join(map(str, bit_vector)), 2)


def parity_check_message_columns(r: int, k: int, col_weight: int) -> np.ndarray:
    """Returns a set of parity columns for the r x k message part of the r x n parity-check matrix."""
    # This is not the most efficient way of finding the columns, but it works!
    ret = np.zeros((r, k), dtype=int)
    i = 0
    c = 0
    while c < k:
        vec = uint_to_bit_vector(i, r)
        vec_sum = np.sum(vec)
        if vec_sum == col_weight:
            ret[:, c] = vec
            c += 1
        i += 1
    return ret


def get_H(k: int, r: int) -> np.ndarray:
    """Generate the r x n parity-check matrix H for a Hsiao SECDED code."""
    # Compute how many message‑bit columns of each odd weight we need
    remaining = k
    weights_counts = []
    w = 3
    while remaining > 0:
        max_cols = math.comb(r, w)
        m = min(max_cols, remaining)
        weights_counts.append((w, m))
        remaining -= m
        w += 2

    # Build and union all message‑bit blocks
    Hm = None
    for w, m in weights_counts:
        block = delta_matrix(r, w, m)
        Hm = block if Hm is None else horizontal_union(Hm, block)

    # Append parity-bit identity
    Hp = np.eye(r, dtype=int)
    H = np.hstack((Hm, Hp))
    return H


def get_G(H: np.ndarray) -> np.ndarray:
    """Generate the k x n generator matrix G for a Hsiao SECDED code with the given r x n parity-check matrix H."""
    r = H.shape[0]
    n = H.shape[1]
    k = n - r
    # Message part of G is identity matrix since we want systematic form.
    G_m = np.identity(k, dtype=int)
    H_m = H[:, :k]
    # Parity part of G is the transpose of the messsage part of H.
    G_p = H_m.T
    G = np.hstack((G_m, G_p))
    return G


def check_columns_unique(matrix: np.ndarray) -> bool:
    """Check that no columns are the same in the given matrix."""
    for ci in range(matrix.shape[1]):
        for cj in range(ci + 1, matrix.shape[1]):
            assert not np.array_equal(matrix[:, ci], matrix[:, cj])
    return True


def check_columns_have_weight(matrix: np.ndarray, weight: int) -> bool:
    """Check that all columns in the given matrix have the same weight."""
    sum_over_rows = np.sum(matrix, axis=0)
    return np.all(sum_over_rows == weight)


def check_column_weights_are_odd(matrix: np.ndarray) -> bool:
    """Check that all columns in the given matrix have an odd weight."""
    sum_over_rows = np.sum(matrix, axis=0)
    return np.all(sum_over_rows % 2 == 1)


def check_row_sums_differ_by_at_most_one(matrix: np.ndarray) -> bool:
    """Check that the row sums of the given matrix differ by at most one."""
    sum_over_columns = np.sum(matrix, axis=1)
    return np.all(np.abs(sum_over_columns - sum_over_columns[0]) <= 1)


def check_matrix_is_binary(matrix: np.ndarray) -> None:
    """Raise a ValueError if the given matrix is not binary (contains only 0s and 1s)."""
    zeros = matrix == 0
    ones = matrix == 1
    if not np.all(zeros + ones):
        matrix_str = np.array2string(
            matrix, separator=", ", threshold=np.inf, max_line_width=np.inf
        )
        err_string = [
            "Matrix contains non-binary values:",
            f"{matrix_str}",
        ]
        raise ValueError("\n".join(err_string))


def binary_matmul(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Multiply two binary matrices (A @ B) and raise a ValueError if the result is not binary."""
    AB = (A @ B) % 2
    return AB


def check_matrices_orthogonal(A: np.ndarray, B: np.ndarray) -> None:
    """Raise a ValueError if two matrices are not orthogonal (A @ B != 0)."""
    AB = binary_matmul(A, B)
    if not np.all(AB == 0):
        A_str = np.array2string(
            A, separator=", ", threshold=np.inf, max_line_width=np.inf
        )
        B_str = np.array2string(
            B, separator=", ", threshold=np.inf, max_line_width=np.inf
        )
        AB_str = np.array2string(
            AB, separator=", ", threshold=np.inf, max_line_width=np.inf
        )
        err_string = [
            "Matrices are not orthogonal.",
            f"A =\n{A_str}",
            f"B =\n{B_str}",
            f"A @ B =\n{AB_str}",
        ]
        raise ValueError("\n".join(err_string))


def hsiao_secded_code(k: int) -> tuple[int, int, np.ndarray, np.ndarray]:
    """Generate a Hsiao SECDED code with the given number of message bits.

    Args:
        k: Number of message bits (k)

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
    if k <= 0:
        raise ValueError("k must be positive.")
    r = get_r(k)
    n = k + r
    H = get_H(k, r)
    G = get_G(H)
    return r, n, H, G


def encode(m: np.ndarray, G: np.ndarray) -> np.ndarray:
    """Encode a message m using the generator matrix G."""
    return binary_matmul(m, G)


def decode_syndrome(c: np.ndarray, H: np.ndarray, k: int) -> np.ndarray:
    """Decode a codeword c to a syndrome using the parity-check matrix H."""
    return binary_matmul(c, H.T)


def decode_message(
    c: np.ndarray, s: np.ndarray, H: np.ndarray
) -> tuple[np.ndarray, bool, bool]:
    """Decode a codeword c to a message using the syndrome s.

    Args:
        c: Codeword of shape (n,)
        s: Syndrome of shape (r,)
        H: Parity-check matrix of shape (r, n)

    Returns:
        tuple[np.ndarray, bool, bool]:
            - Decoded message. Can be valid only if no double-bit error was detected.
            - True if a single-bit error was corrected, False otherwise
            - True if a double-bit error was detected-but-uncorrectable, False otherwise
    """
    n = c.shape[0]
    r = s.shape[0]
    k = n - r
    if H.shape[0] != r or H.shape[1] != n:
        raise ValueError("H must be r x n.")

    # Case 0: Syndrome is zero, no errors detected.
    if np.all(s == 0):
        return (c[:k], False, False)

    # Case 1: Syndrome is for an even number of bits in error, which happens when the syndrome is even in a Hsiao SECDED code.
    # Maximum likelihood decoding produces multiple equiprobable candidate codewords, so treat as detected-but-uncorrectable.
    # NOTE: We are returning *some* message but it is likely to have been corrupted!
    if (np.sum(s) % 2) == 0:
        return (c[:k], False, True)

    # Remaining case: Syndrome is for an odd number of bits in error, which happens when the syndrome is odd in a Hsiao SECDED code.
    # *Usually* this is a single-bit error, which is always closest to exactly one codeword. So with maximum likelihood decoding
    # we can correct it. However, sometimes it can be a three-bit error that is actually detected-but-uncorrectable.
    assert np.sum(s) % 2 == 1
    for ci in range(n):
        # If the syndrome equals a column of H, then we decide the error is in that column and we can correct it.
        if np.array_equal(H[:, ci], s):
            loc = ci
            c[loc] = 1 - c[loc]
            return (c[:k], True, False)

    # If no column of H matches the syndrome, then the codeword is uncorrectable.
    # Similarly to above, we return *some* message but it is likely to have been corrupted!
    return (c[:k], False, True)


def G_col_to_sv(col: np.ndarray, col_idx: int) -> str:
    """Generate a Verilog RTL assignment for a single column of the generator matrix G."""
    xors = []
    nonzero_indices = np.nonzero(col)[0]
    for i in nonzero_indices:
        xors.append(f"m[{i}]")
    return f"    assign parity[{col_idx}] = " + " ^ ".join(xors) + ";"


def G_to_sv(G: np.ndarray) -> str:
    """Generate Verilog RTL code for the given generator matrix G."""
    assigns = []
    # Since we know G is in systematic form, we can just assign the message bits to the codeword bits.
    # We don't need to codegen that part.
    k = G.shape[0]
    r = get_r(k)
    for i in range(r):
        assigns.append(G_col_to_sv(G[:, k + i], i))
    return "\n".join(assigns)


def syndrome_bit_to_sv(row: np.ndarray, row_idx: int) -> str:
    """Generate a Verilog RTL assignment for a single bit of the syndrome."""
    xors = []
    nonzero_indices = np.nonzero(row)[0]
    for i in nonzero_indices:
        xors.append(f"cw[{i}]")
    return f"    assign syndrome[{row_idx}] = " + " ^ ".join(xors) + ";"


def syndrome_to_sv(H: np.ndarray) -> str:
    """Generate Verilog RTL code for the syndrome of the given parity-check matrix H."""
    assigns = []
    r = H.shape[0]
    for i in range(r):
        # Reverse row index (r - i - 1)  because row 0 is actually the MSb of the syndrome
        assigns.append(syndrome_bit_to_sv(H[i, :], r - i - 1))
    return "\n".join(assigns)


def H_col_to_sv(col: np.ndarray, col_idx: int) -> str:
    """Generate a Verilog RTL assignment for a single column of the parity-check matrix H."""
    r = col.shape[0]
    return (
        f"    assign parity_check_matrix[{col_idx}] = {r}'b"
        + "".join(col.astype(str))
        + ";"
    )


def H_to_sv(H: np.ndarray) -> str:
    """Generate Verilog RTL code for the columns of the given parity-check matrix H."""
    assigns = []
    for i in range(H.shape[1]):
        assigns.append(H_col_to_sv(H[:, i], i))
    return "\n".join(assigns)
