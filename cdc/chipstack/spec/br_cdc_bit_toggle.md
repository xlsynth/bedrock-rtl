## Design Mental Model
### File: ./cdc/rtl/br_cdc_bit_toggle.sv

### SUMMARY

#### Module Instantiation Hierarchy:
- br_cdc_bit_toggle
  - br_gate_cdc_maxdel
    - br_gate_buf
  - br_gate_cdc_sync

#### Module Summary Table:
| Module | Summary |
|--------|---------|
| br_cdc_bit_toggle (Top Level) | The "br_cdc_bit_toggle" module is designed to facilitate the safe transfer of a single-bit signal across different clock domains, minimizing the risk of metastability. Its primary functionality is to synchronize the signal using a configurable number of stages, with an optional source flop, ensuring signal integrity and stability during the clock domain crossing. |
| br_gate_buf | The "br_gate_buf" module is a basic buffer used in digital circuits. Its primary purpose is to transfer an input signal to an output without altering the signal, effectively providing signal isolation or driving capability enhancement. |
| br_gate_cdc_maxdel | The "br_gate_cdc_maxdel" module is designed to be used at clock domain crossings where it is crucial to check for maximum delay or skew. Its primary functionality is to act as a buffer, ensuring that the signal integrity is maintained across the crossing, while also indicating the need for timing checks to prevent potential issues due to signal delays. |
| br_gate_cdc_sync | The "br_gate_cdc_sync" module is designed for clock domain crossing synchronization. Its primary functionality is to safely transfer a signal from one clock domain to another by using a series of flip-flops, ensuring that the signal is stable and free from metastability issues. The module allows for parameterization of the number of synchronization stages, providing flexibility in achieving the desired level of signal stability. |

### Clock Ports
|Name|Description|
|---|---|
|src_clk|<br> **Clock active edge:** posedge<br><br>**Input ports in this clock domain:** `src_bit`, `src_rst`<br><br>**Output ports in this clock domain:** None|
|dst_clk|<br> **Clock active edge:** posedge<br><br>**Input ports in this clock domain:** src_bit_internal_maxdel<br><br>**Output ports in this clock domain:** dst_bit<br><br>DUT Input ports: `src_bit`<br><br>DUT Output ports: `dst_bit`|

### Reset Ports
|Name|Description|
|---|---|
|src_rst|<br> **Reset polarity:** Not specified<br><br>**Input ports in this reset domain:** `src_rst`, `src_bit`, `src_clk`<br><br>**Output ports in this reset domain:** None<br><br>DUT Input ports: `src_bit`  <br>DUT Output ports: `dst_bit`|
|dst_rst|<br> **Reset polarity:** Not specified<br><br>**Input ports in this reset domain:** `dst_rst`, `dst_clk`<br><br>**Output ports in this reset domain:** `dst_bit`<br><br>DUT Input ports: `src_bit`  <br>DUT Output ports: `dst_bit`|

### Input Ports
|Name|Description|
|---|---|
|src_bit|**Type:** `logic`.<br><br> **Purpose**: The `src_bit` port serves as the input signal that needs to be synchronized across clock domains.<br><br>**Interaction**: Users or other modules interact with the `src_bit` port by providing a single-bit logic signal that represents the state or event to be transferred from the source clock domain (`src_clk`) to the destination clock domain (`dst_clk`).<br><br>**Expected Behavior**:<br>&nbsp;&nbsp;- When `src_bit` is toggled, it indicates a change or event in the source clock domain that needs to be communicated to the destination clock domain.<br>&nbsp;&nbsp;- The signal is first optionally registered (if `AddSourceFlop` is set to 1) to stabilize it before synchronization.<br>&nbsp;&nbsp;- The synchronized version of `src_bit` is eventually reflected at the `dst_bit` output after passing through the specified number of synchronization stages (`NumStages`).<br><br>**Interesting Behavior**:<br>&nbsp;&nbsp;- If `AddSourceFlop` is enabled, `src_bit` is first registered on the `src_clk` domain, which can help reduce metastability by ensuring a stable input to the synchronizer.<br>&nbsp;&nbsp;- The number of synchronization stages (`NumStages`) directly affects the reliability of the synchronization process. A higher number of stages generally reduces the probability of metastability but increases latency.<br>&nbsp;&nbsp;- The design assumes that `NumStages` is at least 1, ensuring that there is always at least one stage of synchronization to mitigate metastability risks.|

### Output Ports
|Name|Description|
|---|---|
|dst_bit|**Type:** `logic`.<br><br> **Purpose**: The purpose of the `dst_bit` port is to provide a synchronized version of the `src_bit` signal, transferred from the source clock domain (`src_clk`) to the destination clock domain (`dst_clk`).<br><br>**Interaction**: Users or other modules interact with the `dst_bit` port by reading its value to obtain the synchronized state of the `src_bit` signal after it has been processed through the clock domain crossing (CDC) mechanism.<br><br>**Expected Behavior**:<br>&nbsp;&nbsp;- The `dst_bit` reflects the state of the `src_bit` after it has been synchronized across the clock domains.<br>&nbsp;&nbsp;- The synchronization process involves a series of flip-flops determined by the `NumStages` parameter, which defaults to 3, ensuring a low probability of metastability.<br>&nbsp;&nbsp;- If `AddSourceFlop` is set to 1, an additional flip-flop stage is added on the source side before synchronization.<br>&nbsp;&nbsp;- Reset Value: Upon reset, `dst_bit` = 0, as it is not explicitly assigned a value during reset.<br><br>**Interesting Behavior**:<br>&nbsp;&nbsp;- The `dst_bit` may exhibit a delay in reflecting changes from `src_bit` due to the synchronization stages, especially if `NumStages` is increased.<br>&nbsp;&nbsp;- The behavior of `dst_bit` is influenced by the `AddSourceFlop` parameter, which can add an extra stage of delay if enabled.|

### Design Parameters
|Name|Description|
|---|---|
|NumStages|**Type:** `int`.<br><br> **Purpose of the Parameter**:  <br>The `NumStages` parameter determines the number of synchronization stages used in the design to transfer the `src_bit` signal from the source clock domain (`src_clk`) to the destination clock domain (`dst_clk`). This parameter is crucial for reducing the probability of metastability during the clock domain crossing. Users can configure `NumStages` to adjust the level of synchronization based on their specific technology node requirements. A higher number of stages generally increases the robustness of the synchronization process, providing a more reliable transfer of the `src_bit` to `dst_bit` across different clock domains.|
|AddSourceFlop|**Type:** `bit`.<br><br> **Purpose of the Parameter**:  <br>The `AddSourceFlop` parameter determines whether an additional flip-flop is inserted on the source clock domain before the signal is synchronized to the destination clock domain. When set, it introduces a flip-flop that captures the `src_bit` on the `src_clk`, potentially improving signal stability before synchronization. This can be particularly useful in reducing the risk of metastability when transitioning between clock domains. For example, enabling this parameter can help ensure that the `src_bit` is more stable and less prone to glitches before it is processed by the synchronizer stages. Conversely, disabling it allows the `src_bit` to pass directly to the synchronization logic, which might be preferred in scenarios where minimal latency is critical, and the source signal is already stable.|

### Basic Functionality
|Function|Description|
|---|---|
|Signal Synchronization|Description: Synchronizes the input signal `src_bit` from the source clock domain to the destination clock domain using a series of flip-flops, determined by the parameter `NumStages`.<br>Input Signals: src_bit<br>Output Signals: dst_bit<br><br>Transactions:<br><br>Transaction 1:<br>1. The testbench provides a value to `src_bit`.<br>2. The design captures `src_bit` on the rising edge of `src_clk`.<br>3. The design propagates the captured value through a series of flip-flops, determined by the parameter `NumStages`.<br>4. The design outputs the synchronized value on `dst_bit` after the specified number of stages.<br>5. The testbench monitors `dst_bit` to verify the correct synchronized value is output.<br>|
|Source Flop Addition|Description: The purpose of this functionality is to optionally add a flop on the source clock before the synchronizer when `AddSourceFlop` is set to 1, ensuring the input signal `src_bit` is captured before synchronization.<br>Input Signals: src_bit, src_clk<br>Output Signals: dst_bit<br><br>Transactions:<br><br>Transaction 1:<br>1. The testbench sets `src_bit` to a desired logic level (0 or 1).<br>2. The design captures `src_bit` on the rising edge of `src_clk` if `AddSourceFlop` is set to 1.<br>3. The captured value is then propagated through the synchronization stages.<br>4. The design outputs the synchronized value on `dst_bit`.<br>5. The testbench monitors `dst_bit` to verify it matches the expected synchronized value.<br>|
|Signal Propagation with Maximum Delay Check|Description: The purpose of this functionality is to propagate the input signal `src_bit` to the output `dst_bit` using a buffer, while indicating the need for maximum delay checks across clock domain crossings.<br>Input Signals: src_bit<br>Output Signals: dst_bit<br><br>Transactions:<br><br>Transaction 1:<br>1. The testbench sets `src_bit` to a desired logic level (0 or 1).<br>2. The design propagates the value of `src_bit` to `dst_bit` using the buffer.<br>3. The testbench monitors `dst_bit` to verify it matches the value of `src_bit`.<br>4. The design indicates the need for maximum delay checks across the crossing.<br>|
|Signal Integrity Verification|Description: The purpose of this functionality is to ensure that the signal `src_bit` maintains its integrity when crossing from one clock domain to another, using the buffer to indicate the need for maximum delay checks.<br>Input Signals: src_bit<br>Output Signals: dst_bit<br><br>Transactions:<br><br>Transaction 1:<br>1. The testbench sets `src_bit` to a logic level (0 or 1).<br>2. The design propagates the value of `src_bit` to `dst_bit` using the buffer.<br>3. The testbench monitors `dst_bit` to verify it matches the value of `src_bit`.<br>4. The design indicates the need for maximum delay checks across the clock domain crossing.<br>|

### End-to-End Functionality
|Function|Description|
|---|---|
|Signal Synchronization with Optional Source Flop|The RTL design facilitates the safe transfer of a single-bit signal, `src_bit`, from a source clock domain to a destination clock domain, minimizing the risk of metastability. The process begins with the optional addition of a source flop, controlled by the `AddSourceFlop` signal. If `AddSourceFlop` is set to 1, the `src_bit` is captured on the rising edge of the source clock, `src_clk`, before proceeding to synchronization. Regardless of whether the source flop is used, the signal is then passed through a series of flip-flops, the number of which is determined by the `NumStages` parameter. This series of flip-flops ensures that the signal is properly synchronized to the destination clock domain, `dst_clk`. The synchronized signal is finally output as `dst_bit`. The testbench provides a value to `src_bit`, and after the synchronization process, the design outputs the synchronized value on `dst_bit`. This process ensures that the signal is stable and reliable when transferred across clock domains.|
