# QCP: A Practical Separation Logic-based C Program Verification Tool

## 📂 Repository Structure
- `linux-binary/`, `win-binary/`, `mac-arm64-binary`: Precompiled QCP binaries
- `QCP_examples/`: Annotated C programs
- `SeparationLogic/`: Rocq backend to check QCP-generated VCs
- `tutorial/`: Step-by-step QCP usage guide
- `RunningExample-linux.sh`, `RunningExample-windows.sh`: Scripts to run QCP examples

### Prerequisites

- [Rocq (Coq) Platform 8.15](https://rocq-prover.org/)
- `make`

### Build Instructions

1. **Clone the repository**
    ```bash
    git clone https://github.com/yashen32768/ASE25-TOOL-QCP.git
    cd ASE25-TOOL-QCP/
    ```
2. **Configure Makefile in SeparationLogic folder and SeparationLogic/unifysl folder**
    Create a new file named CONFIGURE in folder SeparationLogic and folder SeparationLogic/unifysl, and the content is as follows:
    ```make
    COQBIN=        # Path to your Coq binaries, or leave empty if 'coqc' is in your PATH
    SUF=           # Set to .exe on Windows; leave empty on Linux and MacOS
    ```
3. **Build the separation logic backend**
   ```bash
   cd SeparationLogic/unifysl/
   make depend
   make -j5
   cd ..
   make depend
   make -j5
   ```
3. **Generate `_CoqProject`**
   ```bash
   make _CoqProject
   ```
### Options to run QCP

If you haven't seen our tutorial, we recommend using the directives in our scripts when using QCP, and here is an explanation of some of the compilation parameters.

Usage: ./symexec [options]

We provide the following execution options. Those marked with * are necessary.

  * --input-file=<file>
specify the input C source code.

  * --goal-file=<file>
  * --proof-auto-file=<file>
  * --proof-manual-file=<file-name>
specify generated files. our tool will generate 3 Coq scripts: "goal-file" contains the VCs; "proof-auto-file" contains proofs of automatically solved VCs; "proof-manual-file" contains missing proofs of other VCs.

  --gen-and-backup
if generated files already exist, copy them to backup files before rewrite them; otherwise only "proof-manual" is copied.

  --no-exec-info
ignore the intermediate information during symbolic execution.

  --coq-logic-path=<path>
specify the (Coq) logic path of "goal-file".

  -slp <dir> <path>
add directory which has the logic path to the list of strategy search paths.

  -I<dir>
add directory to the list of include search paths.

If the source file contains preprocessing commands (#define, #include, etc.), please use "cpp -C <input-file> <output-file>" to preprocess it. Currently only "#include" is supported natively.

The outputted .v file needs to be run in conjunction with SeparationLogic. For instructions on how to run SeparationLogic, please refer to SeparationLogic/README.md.
