To run example:
1. Install [python3](https://www.python.org/downloads/) or run `nix-shell` if using nix
2. run `python -m venv .`
3. run `source ./bin/activate` on Linux and maxOS or `.\Scripts\Activate.ps1` on Windows to enter a Python virtual environment
4. run `pip install -r requirements.txt`
6. run `python main.py`
7. run `deactivate` to exit the Python virtual environment

In your actual project, use the `tree-sitter-tlaplus` package instead of a local reference in your `requirements.txt`.

