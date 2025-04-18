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
from itertools import combinations

# Ideally this would be infinity, but the optimal algorithm is prohibitively slow for large k.
# We set this to 256 because that takes a couple minutes and going to 512 would probably take hours.
MAX_K_FOR_OPTIMAL_ALGORITHM = 256


def get_r(k: int) -> int:
    """Calculate the number of parity bits r for a Hsiao SECDED code with k message bits."""
    r = 1
    while r < math.ceil(math.log2(k + r)) + 1:
        r += 1
    return r


def get_Hm(k: int, r: int) -> np.ndarray:
    """
    Find the message part H_m of the Hsiao parity-check matrix H using the
    approach described in reference [2]: recursively balanced Δ-matrices.

    It guarantees the following properties:

    (1) Every column contains an odd number of 1s.
    (2) The total number of 1s reaches the minimum.
    (3) The difference of the number of 1s in any two rows is not greater than 1.
    (4) No two columns are the same.
    """

    def _delta_base(R: int, J: int, m: int) -> np.ndarray:
        """
        Handles the six special "ending state" base cases of generating Δ(R,J,m) described
        in the paper; keeps more 1s at the top of the matrix.

        Δ(R,J,m) is a binary R x m matrix with column weight J, for 0 <= J <= R and all
        columns are unique.
        """
        # The order of the following cases is important to maintain.

        # Empty matrix
        if m == 0:
            # Cannot return None because that would break the recursive construction.
            # Instead, return an empty matrix with the correct shape.
            return np.zeros((R, 0), dtype=int)
        # Column weight of zero -> one column of zeros
        if J == 0:
            return np.zeros((R, 1), dtype=int)
        # Column weight of R -> one column of ones
        if J == R:
            return np.ones((R, 1), dtype=int)
        # Single column -> J ones at top, then R-J zeros
        if m == 1:
            return np.vstack(
                (np.ones((J, 1), dtype=int), np.zeros((R - J, 1), dtype=int))
            )
        # Unit vectors
        if J == 1:
            M = np.zeros((R, m), dtype=int)
            num_rows = min(m, R)
            ones_rows = np.arange(num_rows)
            M[ones_rows, np.arange(m)] = 1
            return M
        # Complements of unit vectors
        if J == R - 1:
            M = np.ones((R, m), dtype=int)
            num_rows = min(m, R)
            starting_row = R - num_rows
            zeros_rows = np.arange(num_rows) + starting_row
            M[zeros_rows, np.arange(m)] = 0
            return M
        # Not a base case
        return None

    def _delta_matrix_recursive(R: int, J: int, m: int) -> np.ndarray:
        """
        Recursively build Δ(R,J,m) with equal-weight columns and quasi-equal-weight rows
        (row sums differ by ≤ 1).  Implements Algorithm A' + improved row-rotation (§4).

        This algorithm is O(R * m * (log R + log m)) in the average case.
        """
        base = _delta_base(R, J, m)
        if base is not None:
            return base

        # Step 2: choose split size  m1 = ⌊m·J/R + (R−1)/R⌋
        m1 = math.floor(m * J / R + (R - 1) / R)
        Δ1 = _delta_matrix_recursive(R - 1, J - 1, m1)
        Δ2 = _delta_matrix_recursive(R - 1, J, m - m1)

        # Improved row‑rotation for quasi‑balance (paper Sec. 4)
        r1 = ((J - 1) * m1) % (R - 1)  # Equation (8)
        r2 = (J * (m - m1)) % (R - 1)  # Equation (9)

        if (r1 + r2) > (R - 1):
            rprime = r1 + r2 - (R - 1)
            assert r1 > rprime
            assert r2 > rprime
            shift = r2 - rprime
            Δ2prime = np.vstack((Δ2[shift:], Δ2[:shift]))
        else:
            top, rest = Δ2[:r2], Δ2[r2:]
            Δ2prime = np.vstack((rest[:r1], top, rest[r1:]))

        # Assemble the R × m block as in Equation (6)
        top_row = np.hstack((np.ones(m1, int), np.zeros(m - m1, int)))[None, :]
        bottom = np.hstack((Δ1, Δ2prime))
        return np.vstack((top_row, bottom))

    remaining = k
    Hm = None
    for J in range(3, r + 1, 2):
        max_cols = math.comb(r, J)
        take = min(max_cols, remaining)
        if take == 0:
            continue
        block = _delta_matrix_recursive(r, J, take)
        Hm = block if Hm is None else np.hstack((Hm, block))
        remaining -= take
        if remaining == 0:
            break
    return Hm


def get_Hm_greedy_suboptimal(k: int, r: int) -> np.ndarray:
    """
    Generate the message part Hm of the Hsiao parity-check matrix H using a greedy algorithm
    that guarantees the following properties described in reference [2]:

    (1) Every column contains an odd number of 1s.
    (2) The total number of 1s reaches the minimum.
    (4) No two columns are the same.

    It does NOT guarantee the following property:

    (3) The difference of the number of 1s in any two rows is not greater than 1.

    Because property (3) is not guaranteed, the algorithm is not optimal and therefore
    this isn't technically a Hsiao code, but it is still a valid SECDED code.

    You probably only want to use this if finding the optimal Hm is prohibitively slow,
    e.g., when k is large.
    """

    def parity_check_message_columns(r: int, k: int, col_weight: int) -> np.ndarray:
        """
        Returns a set of parity columns for the r x k message part of the
        r x n parity-check matrix, by walking the first k combinations
        of r choose col_weight.
        """
        ret = np.zeros((r, k), dtype=int)
        # itertools.combinations(range(r), col_weight) yields tuples of indices
        # at which bits should be 1.  We just take the first k of them.
        for c, ones in enumerate(combinations(range(r), col_weight)):
            ret[list(ones), c] = 1
            if c + 1 == k:
                break
        return ret

    n = k + r
    # Fill H_m with column vectors that satisfy conditions (1), (2), and (4).
    start_col = 0
    weight = 3  # Only use odd weights, and skip weight 1 since it's only used for H_p
    Hm = np.zeros((r, k), dtype=int)
    while start_col < k:
        remaining_cols = k - start_col
        cols_using_weight = min(math.comb(r, weight), remaining_cols)
        end_col = start_col + cols_using_weight
        Hm[:, start_col:end_col] = parity_check_message_columns(
            r, cols_using_weight, weight
        )
        start_col = end_col
        weight += 2  # Only use odd weights
    return Hm


def get_H(k: int, r: int) -> np.ndarray:
    """Generate the r x n parity-check matrix H for a Hsiao SECDED code."""
    # Build a perfectly row-balanced message matrix of k odd-weight columns
    if k <= MAX_K_FOR_OPTIMAL_ALGORITHM:
        Hm = get_Hm(k, r)
    else:
        Hm = get_Hm_greedy_suboptimal(k, r)
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


def binary_matmul(A: np.ndarray, B: np.ndarray) -> np.ndarray:
    """Multiply two binary matrices (A @ B) and raise a ValueError if the result is not binary."""
    AB = (A @ B) % 2
    return AB


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


def check_construction(
    G: np.ndarray,
    H: np.ndarray,
    check_code_distance: bool = True,
    check_row_balance: bool = True,
) -> None:
    """Raises a ValueError if the given generator matrix G and parity-check matrix H are not a valid Hsiao SECDED code."""

    def check_columns_unique(matrix: np.ndarray) -> None:
        """Raises a ValueError if any columns are the same in the given matrix."""
        for ci in range(matrix.shape[1]):
            for cj in range(ci + 1, matrix.shape[1]):
                if np.array_equal(matrix[:, ci], matrix[:, cj]):
                    raise ValueError("Columns are not unique.")

    def check_column_weights_are_odd(matrix: np.ndarray) -> None:
        """Raises a ValueError if any columns in the given matrix do not have an odd weight."""
        sum_over_rows = np.sum(matrix, axis=0)
        if not np.all(sum_over_rows % 2 == 1):
            err_string = [
                "Columns do not have an odd weight.",
                f"matrix = \n{matrix}",
                f"sums = \n{sum_over_rows}",
            ]
            raise ValueError("\n".join(err_string))

    def check_minimum_total_weight(H: np.ndarray) -> None:
        """
        Raise a ValueError if the total number of 1s in H exceeds the lower bound.
        (Hsiao codes purport to achieve the lower bound.)
        """

        def minimal_total_weight(r: int, k: int) -> int:
            """
            Calculate the minimal total number of 1s for an r x n Hsiao parity-check matrix,
            based on selecting the k odd-weight columns of smallest weight. n = r + k.
            """
            total = 0
            remaining = k
            for J in range(3, r + 1, 2):
                count = math.comb(r, J)
                take = min(count, remaining)
                total += take * J
                remaining -= take
                if remaining == 0:
                    break
            # Add on the identity matrix of parity bits (systematic form)
            total += r
            return total

        r, n = H.shape
        k = n - r
        actual = int(np.sum(H))
        minimal = minimal_total_weight(r, k)
        if actual != minimal:
            err = [
                "Total weight of H is not minimal.",
                f"actual weight = {actual}",
                f"minimal weight = {minimal}",
                f"H = \n{H}",
            ]
            raise ValueError("\n".join(err))

    def check_distance_ge_4(H: np.ndarray) -> None:
        """Raises a ValueError if the distance of the code is less than 4."""
        r, n = H.shape
        # test every subset of 1, 2, or 3 columns
        for t in (1, 2, 3):
            for cols in combinations(range(n), t):
                sub = H[:, cols]  # shape r×t
                # over GF(2), independence means sub @ x = 0 only for x=0
                # but with t<=r we can check rank = t:
                if np.linalg.matrix_rank(sub) < t:
                    err_string = [
                        "Minimum distance of H is less than 4 (required for a SECDED code).",
                        f"columns are dependent --> distance < 4: {cols}",
                        f"H = \n{H}",
                    ]
                    raise ValueError("\n".join(err_string))

    def check_row_sums_differ_by_at_most(matrix: np.ndarray, max_diff: int) -> None:
        """Raises a ValueError if the row sums of the given matrix differ by more than max_diff."""
        sum_over_columns = np.sum(matrix, axis=1)
        if not np.all(np.abs(sum_over_columns - sum_over_columns[0]) <= max_diff):
            err_string = [
                f"Row sums differ by more than {max_diff}.",
                f"matrix = \n{matrix}",
                f"row sums = \n{sum_over_columns}",
            ]
            raise ValueError("\n".join(err_string))

    def check_matrix_is_binary(matrix: np.ndarray) -> None:
        """Raises a ValueError if the given matrix is not binary (contains only 0s and 1s)."""
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

    def check_matrices_orthogonal(A: np.ndarray, B: np.ndarray) -> None:
        """Raises a ValueError if two matrices are not orthogonal (A @ B != 0)."""
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

    def check_G_systematic(G: np.ndarray) -> bool:
        """Raises a ValueError if the given generator matrix G is not in systematic form."""
        k = G.shape[0]
        I_k = np.identity(k, dtype=int)
        if not np.array_equal(G[:, :k], I_k):
            raise ValueError("Generator matrix G is not in systematic form.")

    def check_H_systematic(H: np.ndarray) -> None:
        """Raises a ValueError if the given parity-check matrix H is not in systematic form."""
        r, n = H.shape
        k = n - r
        I_r = np.identity(r, dtype=int)
        if not np.array_equal(H[:, k:], I_r):
            raise ValueError("Parity-check matrix H is not in systematic form.")

    check_matrix_is_binary(G)
    check_matrix_is_binary(H)
    check_columns_unique(G)
    check_columns_unique(H)
    check_matrices_orthogonal(G, H.T)
    if check_code_distance:
        check_distance_ge_4(H)
    check_column_weights_are_odd(H)
    check_minimum_total_weight(H)
    if check_row_balance:
        check_row_sums_differ_by_at_most(H, 1)
    check_G_systematic(G)
    check_H_systematic(H)
