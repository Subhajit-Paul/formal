import argparse
import sys
import os

from pyverilog.vparser.parser import parse
from pyverilog.vparser.ast import ModuleDef, Ioport, Input, Decl

def get_input_ports_from_module(mod):
    inputs = set()
    portlist = mod.portlist
    if portlist is not None:
        if hasattr(portlist, 'ports'):
            ports = portlist.ports
        else:
            ports = [c for c in portlist.children()]
        for p in ports:
            if isinstance(p, Ioport):
                decl = p.first
                if isinstance(decl, Input):
                    inputs.add(decl.name)
            elif isinstance(p, Input):
                inputs.add(p.name)
            # elif isinstance(p, Inout):
            #     inputs.add(p.name)
            # else: ignore output / other port types here
            
    for item in mod.items:
        if isinstance(item, Decl):
            for decl_child in item.list:  
                if isinstance(decl_child, Input):
                    inputs.add(decl_child.name)

    return sorted(inputs)

def extract_input_signals(ast):
    module_inputs = {}
    for definition in ast.description.definitions:
        if isinstance(definition, ModuleDef):
            modname = definition.name
            inputs = get_input_ports_from_module(definition)
            module_inputs[modname] = inputs
    return module_inputs

def main():
    parser = argparse.ArgumentParser(description="Extract input signal names from Verilog/SystemVerilog file using Pyverilog.")
    parser.add_argument("files", nargs="+", help="Verilog/SystemVerilog file(s) to parse")
    parser.add_argument("-I", "--include", action="append", dest="incdirs", default=[],
                        help="Include path for `include files. Can be given multiple times.")
    parser.add_argument("-D", "--define", action="append", dest="defines", default=[],
                        help="Macro definitions for preprocessing. Can be given multiple times.")
    parser.add_argument("-v", "--verbose", action="store_true", dest="verbose",
                        help="Verbose output: show module names with inputs")
    args = parser.parse_args()

    # Check files exist
    for f in args.files:
        if not os.path.isfile(f):
            print(f"Error: file not found: {f}", file=sys.stderr)
            sys.exit(1)

    # Check include directories
    for d in args.incdirs:
        if not os.path.isdir(d):
            print(f"Warning: include directory {d} not found", file=sys.stderr)

    try:
        ast, directives = parse(args.files,
                                preprocess_include=args.incdirs,
                                preprocess_define=args.defines)
    except Exception as e:
        print(f"Error parsing files {args.files}: {e}", file=sys.stderr)
        sys.exit(1)

    module_inputs = extract_input_signals(ast)

    if args.verbose:
        for modname, inputs in module_inputs.items():
            print(f"Module: {modname}")
            if inputs:
                for name in inputs:
                    print(f"  input: {name}")
            else:
                print("  (no input signals found)")
    else:
        multiple = len(module_inputs) > 1
        for modname, inputs in module_inputs.items():
            for name in inputs:
                if multiple:
                    print(f"{modname}:{name}")
                else:
                    print(name)

if __name__ == "__main__":
    main()
