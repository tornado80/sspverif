# /// script
# requires-python = ">=3.13"
# dependencies = [
#   "lark==1.2.2"
# ]
# ///

# Example usage: pipx run tls13-ks-game-gen.py .

import os
import operator
import lark
import argparse
import pydot
import networkx as nx

arg_parser = argparse.ArgumentParser(
                    prog='TLS 1.3 Key Schedule Security Game/Proof Generator',
                    description='Generates games and proof files')
arg_parser.add_argument("project_dir", help="Location of the project directory containing ssp.toml")
args = arg_parser.parse_args()

PROJECT_DIR = args.project_dir
PACKAGES_DIR = os.path.join(PROJECT_DIR, "packages")
GAMES_DIR = os.path.join(PROJECT_DIR, "games")
PROOF_DIR = os.path.join(PROJECT_DIR, "proofs")
PROOF_FILE_PATH = os.path.join(PROOF_DIR, "proof.ssp")

GAMES = ["Gks0", "Gks0Map", "GksMapXpd", "Gks1"]

ADVERSARY_COMPOSITIONS = {
    "Gks0": {
        "GET": "OutputKeyGetter",
        "SET": "ExternalPskSetter",
        "DHGEN": "DH",
        "DHEXP": "DH",
        "XTR": "Xtr",
        "XPD": "Check"
    },
    "Gks0Map": {
        "GET": "Map",
        "SET": "Map",
        "DHGEN": "Map",
        "DHEXP": "Map",
        "XTR": "Map",
        "XPD": "Check"
    },
    "GksMapXpd": {
        "GET": "Map",
        "SET": "Map",
        "DHGEN": "Map",
        "DHEXP": "Map",
        "XTR": "Map",
        "XPD": "Check"
    },
    "Gks1": {
        "GET": "Map",
        "SET": "Map",
        "DHGEN": "Map",
        "DHEXP": "Map",
        "XTR": "Map",
        "XPD": "Check"
    },
}

CHECK_PACKAGE_COMPOSITIONS = {
    "Gks0": {
        "XPD": "Xpd",
        "GET": "Key"
    },
    "Gks0Map": {
        "XPD": "Map",
        "GET": "Map"
    },
    "GksMapXpd": {
        "XPD": "MapXpd",
        "GET": "Map"
    },
    "Gks1": {
        "XPD": "MapXpdRemap",
        "GET": "Map"
    }
}

def get_check_package_compositions(game):
    check_package_compositions = {
        "IS_BIND_KEY": "Names",
        "IS_EARLY_SEPARATION_POINT": "Names",
        "IS_POST_DH_SEPARATION_POINT": "Names",
        "GET_BINDER_KEY": "Names"
    }
    check_package_compositions.update(CHECK_PACKAGE_COMPOSITIONS[game])
    return check_package_compositions

class ParameterExtractor(lark.visitors.Visitor_Recursive):
    def __init__(self):
        self.parameters = {}

    def decl_spec(self, decl):
        identifier, tipe = decl.children
        self.parameters[identifier.value] = (tipe.meta.start_pos, tipe.meta.end_pos)

class AssumptionsAndGamehopsExtractor(lark.visitors.Visitor_Recursive):
    def __init__(self):
        self.assumptions_range = None
        self.game_hops_range = None

    def assumptions(self, assumptions):
        self.assumptions_range = (assumptions.meta.start_pos, assumptions.meta.end_pos)

    def game_hops(self, game_hops):
        self.game_hops_range = (game_hops.meta.start_pos, game_hops.meta.end_pos)

print("Building SSP parser")
parser = lark.Lark.open("ssp.lark", rel_to=__file__, propagate_positions=True)
packages_parameters = {}
for entry in os.listdir(PACKAGES_DIR):
    if entry.endswith(".pkg.ssp"):
        print("Extracting parameters from package", entry)
        instance_name = entry.removesuffix(".pkg.ssp")
        with open(os.path.join(PACKAGES_DIR, entry)) as f:
            content = f.read()
        tree = parser.parse(content)
        extractor = ParameterExtractor()
        extractor.visit_topdown(tree)
        package_parameters = {}
        packages_parameters[instance_name] = package_parameters
        for parameter, (start_pos, end_pos) in extractor.parameters.items():
            package_parameters[parameter] = content[start_pos:end_pos]

game_abstract_functions_signatures = {}
all_abstract_functions_signatures = {}
for game in GAMES:
    print(f"Generating package instances for {game}:")
    graph = pydot.Dot(game)
    nxgraph = nx.DiGraph()
    dependency_graph = nx.DiGraph()
    instances_parameters = {}
    instances_compositions = {}
    instances = set()
    abstract_functions_signatures = {}
    instances_names = {"adversary": "adversary"}
    stack = ["adversary"]
    while len(stack) > 0:
        instance = stack.pop(0)
        if instance in instances:
            continue
        elif instance != "adversary":
            instances.add(instance)
        instances_compositions[instance] = {}
        instances_parameters[instance] = {}
        match instance:
            case "adversary":
                instances_compositions[instance] = ADVERSARY_COMPOSITIONS[game]
            case "OutputKeyGetter":
                instances_compositions[instance] = {
                    "GET": "Key",
                    "IS_OUTPUT_KEY": "Names"
                }
            case "Key":
                instances_compositions[instance] = {
                    "GET_KEY_PACKAGE_IDEALIZATION_PARAMETER": "Parameters",
                    "SAMPLE": "Sample",
                    "UNQ": "Log",
                    "Q": "Log",
                    "IS_DH_KEY": "Names",
                    "IS_PSK": "Names",
                    "IS_0salt_HANDLE": "Handles",
                    "IS_0ikm_HANDLE": "Handles",
                    "IS_noPSK_HANDLE": "Handles",
                    "IS_noDH_HANDLE": "Handles"
                }
            case "Parameters":
                instances_parameters[instance] = {
                    "game": GAMES.index(game)
                }
                instances_compositions[instance] = {
                    "IS_HANDSHAKE_SECRET": "Names",
                    "IS_INTERNAL_KEY": "Names",
                    "IS_DH_KEY": "Names",
                    "IS_PSK": "Names",
                    "IS_OUTPUT_KEY": "Names"
                }
            case "ExternalPskSetter":
                instances_compositions[instance] = {
                    "SET": "Key",
                    "GET_PSK_NAME": "Names"
                }
            case "DH":
                instances_compositions[instance] = {
                    "SET": "Key",
                    "GET_DH_NAME": "Names"
                }
            case "Xtr":
                instances_compositions[instance] = {
                    "GET_XTR_PACKAGE_IDEALIZATION_PARAMETER": "Parameters",
                    "IS_XTR_KEY": "Names",
                    "PARENTS": "Names",
                    "SAMPLE": "Sample",
                    "GET": "Key",
                    "xtr": "xtr0",
                    "SET": "Key"
                }
            case "Check":
                instances_compositions[instance] = get_check_package_compositions(game)
            case "Xpd":
                instances_compositions[instance] = {
                    "IS_XPD_KEY": "Names",
                    "PARENTS": "Names",
                    "LABEL": "Labels",
                    "GET": "Key",
                    "SET": "Key",
                    "xpd": "xpd0",
                    "HASH": "Hash"
                }
            case "Map":
                instances_compositions[instance] = {
                    "SET": "Key",
                    "GET": "Key",
                    "GET_PSK_NAME": "Names",
                    "GET_DH_NAME": "Names",
                    "DHGEN": "DH",
                    "DHEXP": "DH",
                    "XPD": "Xpd",
                    "XTR": "Xtr",
                    "LABEL": "Labels",
                    "PARENTS": "Names",
                    "IS_XTR_KEY": "Names",
                    "IS_XPD_KEY": "Names",
                    "IS_OUTPUT_KEY": "Names",
                    "IS_PSK": "Names",
                    "LEVEL": "Handles",
                    "GETMAP": "MapTable",
                    "SETMAP": "MapTable"
                }
            case "MapTable":
                instances_compositions[instance] = {
                    "IS_noPSK_HANDLE": "Handles",
                    "IS_noDH_HANDLE": "Handles",
                    "IS_0salt_HANDLE": "Handles",
                    "IS_0ikm_HANDLE": "Handles",
                    "GET_DH_NAME": "Names"
                }
            case "MapXpd":
                instances_compositions[instance] = {
                    "IS_OUTPUT_KEY": "Names",
                    "LABEL": "Labels",
                    "PARENTS": "Names",
                    "SET": "Key",
                    "GET": "Key",
                    "XPD": "Map",
                    "GETMAP": "MapTable",
                    "SETMAP": "MapTable",
                    "HASH": "Hash",
                    "xpd": "xpd0",
                }
            case "MapXpdRemap":
                instances_compositions[instance] = {
                    "IS_OUTPUT_KEY": "Names",
                    "LABEL": "Labels",
                    "PARENTS": "Names",
                    "SET": "Key",
                    "GET": "Key",
                    "XPD": "Map",
                    "GETMAP": "MapTable",
                    "SETMAP": "MapTable",
                    "HASH": "Hash",
                    "xpd": "xpd0",
                }
            case "Hash":
                instances_compositions[instance] = {
                    "hash": "hash0",
                    "GET_HASH_PACKAGE_IDEALIZATION_PARAMETER": "Parameters"
                }
            case "Log":
                instances_compositions[instance] = {
                    "GET_LOG_PACKAGE_PARAMETERS": "Parameters",
                    "IS_INFINITY_MAPPING": "Parameters",
                    "IS_1_MAPPING": "Parameters",
                    "IS_A_PATTERN": "Parameters",
                    "IS_D_PATTERN": "Parameters",
                    "IS_F_PATTERN": "Parameters",
                }
            case "Handles" | "xtr0" | "xpd0" | "hash0" | "Labels" | "Sample" | "Names":
                continue
            case p:
                raise NotImplementedError(f"Can not handle package {p}")
        node = pydot.Node(instance, label=instance, shape="rectangle")
        if not nxgraph.has_node(instance):
            dependency_graph.add_node(instance)
            nxgraph.add_node(instance)
        graph.add_node(node)
        for oracle, package in set(instances_compositions[instance].items()):
            graph.add_edge(pydot.Edge(instance, package, label=oracle))
            if not nxgraph.has_node(package):
                nxgraph.add_node(package)
                dependency_graph.add_node(package)
            nxgraph.add_edge(instance, package)
            dependency_graph.add_edge(package, instance)
            stack.append(package)
    is_planar, certificate = nx.check_planarity(nxgraph, counterexample=True)
    #print("Is graph planar?", is_planar)
    counterexample_svg_path = os.path.join(GAMES_DIR, f"{game}_planarity_counterexample.svg")
    if not is_planar and not os.path.exists(counterexample_svg_path):
        nx.drawing.nx_pydot.to_pydot(certificate).write_svg(counterexample_svg_path)
        print("Call graph is not planar, see", counterexample_svg_path)
    game_svg = os.path.join(GAMES_DIR, f"{game}.svg")
    if not os.path.exists(game_svg):
        nx.drawing.nx_pydot.to_pydot(nxgraph).write_svg(game_svg)
        print("Visualized call graph, see", game_svg)
    print("Constructed call graph")
    
    # extract abstract functions
    for instance in instances:
        package_parameters = instances_parameters[instance]
        for parameter, value in packages_parameters[instance].items():
            if parameter not in package_parameters:
                package_parameters[parameter] = parameter
                abstract_functions_signatures[parameter] = value
                all_abstract_functions_signatures[parameter] = value
    game_abstract_functions_signatures[game] = abstract_functions_signatures.keys()
    print("Extracted parameters")

    # give concrete names to instances
    for instance in instances:
        instances_names[instance] = "_".join(["pkg", instance])

    # generate game files
    lines = [f"composition {game} {{\n"]
    for name, signature in sorted(abstract_functions_signatures.items()):
        lines.append(f"    const {name}: {signature};\n")
    lines.append("\n")
    for instance in nx.lexicographical_topological_sort(dependency_graph):
        if instance == "adversary":
            continue
        lines.append(f"    instance {instances_names[instance]} = {instance} {{\n")
        if len(instances_parameters[instance]) > 0:
            lines.append("        params {\n")
            for parameter, value in sorted(instances_parameters[instance].items()):
                lines.append(f"            {parameter}: {value},\n")
            lines.append("        }\n")
        lines.append("    }\n")
        lines.append("\n")
    lines.append("    compose {\n")
    for instance in nx.lexicographical_topological_sort(dependency_graph):
        dependencies = instances_compositions[instance]
        if len(dependencies) == 0:
            continue
        lines.append(f"        {instances_names[instance]}: {{\n")
        for imported_oracle, imported_instance in sorted(dependencies.items(), key=operator.itemgetter(0)):
            lines.append(f"            {imported_oracle}: {instances_names[imported_instance]},\n")
        lines.append(f"        }},\n")
    lines.append("    }\n")
    lines.append("}\n")

    with open(os.path.join(GAMES_DIR, f"{game}.comp.ssp"), "w") as f:
        f.writelines(lines)
    print("Generated game file")

# generate proof file
proof_lines = ["proof Proof {\n"]
for name, signature in sorted(all_abstract_functions_signatures.items()):
    proof_lines.append(f"    const {name}: {signature};\n")
proof_lines.append("\n")
for game in GAMES:
    proof_lines.append(f"    instance game_{game} = {game} {{\n")
    proof_lines.append("        params {\n")
    for name in sorted(game_abstract_functions_signatures[game]):
        proof_lines.append(f"            {name}: {name},\n")
    proof_lines.append("        }\n")
    proof_lines.append("    }\n")
    proof_lines.append("\n")
proof_lines.append("}\n")

if not os.path.exists(PROOF_FILE_PATH):
    with open(PROOF_FILE_PATH, "w") as f:
        f.writelines(proof_lines)
else:
    content = open(PROOF_FILE_PATH).read()
    tree = parser.parse(content)
    extractor = AssumptionsAndGamehopsExtractor()
    extractor.visit_topdown(tree)
    if extractor.assumptions_range is not None:
        assumptions = content[extractor.assumptions_range[0]:extractor.assumptions_range[1]]
        proof_lines.insert(-1, f"    {assumptions}\n\n")
    game_hops = content[extractor.game_hops_range[0]:extractor.game_hops_range[1]]
    proof_lines.insert(-1, f"    {game_hops}\n")
    #os.makedirs(os.path.join(PROOF_DIR, "autogenerated"), exist_ok=True)
    #with open(os.path.join(PROOF_DIR, "autogenerated", "proof.ssp"), "w") as f:
    #    f.writelines(proof_lines)
    with open(PROOF_FILE_PATH, "w") as f:
        f.writelines(proof_lines)

print("Updated proof file")