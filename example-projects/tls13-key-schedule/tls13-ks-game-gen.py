# /// script
# requires-python = ">=3.13"
# dependencies = [
#   "lark==1.2.2"
# ]
# ///

# Example usage: pipx run tls13-ks-game-gen.py . 3

import itertools
import os
import operator
import lark
import argparse

arg_parser = argparse.ArgumentParser(
                    prog='TLS 1.3 Key Schedule Security Package/Game/Proof Generator',
                    description='Generates packages, games, and proof files')
arg_parser.add_argument("project_dir", help="Location of the project directory containing ssp.toml")
arg_parser.add_argument("resumption_levels", type=int, help="Numebr of resumption levels to generate packages and games")
args = arg_parser.parse_args()

PROJECT_DIR = args.project_dir
PACKAGES_DIR = os.path.join(PROJECT_DIR, "packages")
GAMES_DIR = os.path.join(PROJECT_DIR, "games")
PROOF_DIR = os.path.join(PROJECT_DIR, "proofs")
PROOF_FILE_PATH = os.path.join(PROOF_DIR, "proof.ssp")

RESUMPTION_LEVELS = args.resumption_levels
LEVELS_COUNT = RESUMPTION_LEVELS + 1

GAMES = ["Gks0", "Gks0Map", "GksMapXpd", "Gks1"]
GAMES_BEFORE_IDEALIZATION = ["Gks0", "Gks0Map"]
GAMES_AFTER_IDEALIZATION = ["GksMapXpd", "Gks1"]

SEPARATION_POINTS = [
    "bind", # based on resumption bit
    "cet", "eem", # early, i.e. based on binder tag/key
    "cht", "sht", "cat", "sat", "eam", "rm" # other, i.e. based on both DH and binder tag/key
]

PARENT = {
    "psk": "rm",
    "rm": "as",
    "cat": "as",
    "sat": "as",
    "eam": "as",
    "as": ("hsalt", "0ikm"),
    "cht": "hs",
    "sht": "hs",
    "hsalt": "hs",
    "hs": ("esalt", "dh"),
    "binder": "bind",
    "cet": "es",
    "eem": "es",
    "bind": "es",
    "esalt": "es",
    "es": ("0salt", "psk")
}

# TODO: compute the following sets with PARENT
KEYS = ["psk", "hs", "es", "as", "rm", "esalt", "hsalt", "bind", "binder", "eem", "cet", "sht", "cht", "cat", "sat", "eam", "dh", "0ikm", "0salt"]
XTR_KEYS = ["es", "as", "hs"]
XPD_KEYS = ["bind", "binder", "cet", "eem", "esalt", "cht", "sht", "hsalt", "cat", "sat", "eam", "rm", "psk"]
INTERNAL_KEYS = ["esalt", "hsalt", "bind", "es", "as", "hs", "rm"]
OUTPUT_KEYS = ["binder", "cet", "eem", "cht", "sht", "cat", "sat", "eam"]

MAPPING = {
    0: 0,
    1: 1,
    "inf": 2
}
PATTERN = {
    "Z": 0,
    "A": 1,
    "D": 2,
    "F": 3
}

def key_category(key_name):
    if key_name == "dh":
        return "dh"
    if key_name == "psk":
        return "psk"
    if key_name in INTERNAL_KEYS:
        return "internal"
    if key_name in OUTPUT_KEYS:
        return "output"

LOG_PACKAGE_PARAMETERS = {
    "Gks0": {
        "dh": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["Z"]
        },
        "psk": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["A"]
        },
        "internal": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["Z"]
        },
        "output": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["Z"]
        }
    },
    "Gks0Map": {
        "dh": {
            "mapping": MAPPING["inf"],
            "pattern": PATTERN["Z"]
        },
        "psk": {
            "mapping": MAPPING[1],
            "pattern": PATTERN["A"]
        },
        "internal": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["Z"]
        },
        "output": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["Z"]
        }
    },
    "GksMapXpd": {
        "dh": {
            "mapping": MAPPING["inf"],
            "pattern": PATTERN["Z"]
        },
        "psk": {
            "mapping": MAPPING[1],
            "pattern": PATTERN["D"]
        },
        "internal": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["D"]
        },
        "output": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["F"]
        }
    },
    "Gks1": {
        "dh": {
            "mapping": MAPPING["inf"],
            "pattern": PATTERN["Z"]
        },
        "psk": {
            "mapping": MAPPING[1],
            "pattern": PATTERN["D"]
        },
        "internal": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["D"]
        },
        "output": {
            "mapping": MAPPING[0],
            "pattern": PATTERN["F"]
        }
    },
}

def get_log_package_parameters(game, key_name):
    params = LOG_PACKAGE_PARAMETERS[game][key_category(key_name)].copy()
    return params

def get_key_package_parameters(game, key_name, level):
    params = {
        "n": KEYS.index(key_name),
        "l": level
    }
    if game in GAMES_BEFORE_IDEALIZATION:
        if key_name == "psk":
            params["b"] = "true" if level == 0 else "false"
        elif key_name in INTERNAL_KEYS or key_name in OUTPUT_KEYS:
            params["b"] = "false"
    if game in GAMES_AFTER_IDEALIZATION:
        params["b"] = "true"
    return params

def get_key_package_compositions(key_name):
    return {
        "SAMPLE": "Sample",
        "Q": ("Log", key_name),
        "UNQ": ("Log", key_name)
    }

def get_xtr_package_parameters(game, key_name, level):
    params = {
        "n": KEYS.index(key_name),
        "l": level
    }
    if game in GAMES_BEFORE_IDEALIZATION:
        params["b"] = "false"
    if game in GAMES_AFTER_IDEALIZATION:
        if key_name == "hs":
            params["b"] = "true"
        else:
            params["b"] = "false"
    return params

def get_xtr_package_compositions(key_name, level):
    parent1, parent2 = PARENT[key_name]
    return {
        "SAMPLE": "Sample",
        "GET1": ("KeyAdapter", parent1, level),
        "GET2": ("KeyAdapter", parent2, level),
        "xtr": "xtr0",
        "SET": ("Key", key_name, level)
    }

def get_map_xtr_package_compositions(key_name, level):
    parent1, parent2 = PARENT[key_name]
    return {
        "XTR": ("Xtr", key, level),
        "GETMAP1": ("MapAdapter", parent1, level),
        "GETMAP2": ("MapAdapter", parent2, level),
        "SETMAP": ("MapTable", key, level)
    }

def get_xpd_package_parameters(key_name, level):
    return {
        "n": KEYS.index(key_name),
        "l": level
    }

def get_xpd_package_compositions(key_name, level):
    return {
        "LABEL": "Labels",
        "GET": ("Key", PARENT[key_name], level),
        "SET": ("Key", key_name, level + 1 if key_name == "psk" else level),
        "xpd": "xpd0",
        "HASH": "Hash"
    }

def get_map_xpd_package_compositions(key_name, level):
    return {
        "XPD": ("Xpd", key_name, level),
        "GETMAP": ("MapTable", PARENT[key_name], level),
        "SETMAP": ("MapTable", key_name, level + 1 if key_name == "psk" else level),
        "LABEL": "Labels"
    }

def get_map_xpd_output_key_inline_package_compositions(key_name, level):
    return {
        "LABEL": "Labels",
        "GET": ("Key", PARENT[key_name], level),
        "SET": ("Key", key_name, level),
        "xpd": "xpd0",
        "HASH": "Hash",
        "GETMAP": ("MapTable", PARENT[key], level),
        "SETMAP": ("MapTable", key, level)
    }

def get_map_xpd_output_key_remap_package_compositions(key_name, level):
    return {
        "LABEL": "Labels",
        "GET": ("Key", PARENT[key_name], level),
        "SET": ("Key", key_name, level),
        "xpd": "xpd0",
        "HASH": "Hash",
        "GETMAP": ("MapTable", PARENT[key], level),
        "SETMAP": ("MapTable", key, level)
    }

def get_get_output_key_package_compositions(game, key_name, level):
    match game:
        case "Gks0":
            return {"GET": ("Key", key_name, level)}
        case "Gks1" | "Gks0Map" | "GksMapXpd":
            return {"GET": ("MapGetOutputKey", key_name, level)}

def get_check_package_compositions(game, key, level):
    match game:
        case "Gks0":
            return {
                "XPD": ("Xpd", key, level),
                "GET": ("Key", "binder", level)
            }
        case "Gks0Map":
            return {
                "XPD": ("MapXpd", key, level),
                "GET": ("MapGetOutputKey", "binder", level),
            }
        case "GksMapXpd":
            return {
                "XPD": ("MapXpdOutputKeyInline", key, level) if key in OUTPUT_KEYS else ("MapXpd", key, level),
                "GET": ("MapGetOutputKey", "binder", level),
            }
        case "Gks1":
            return {
                "XPD": ("MapXpdOutputKeyRemap", key, level) if key in OUTPUT_KEYS else ("MapXpd", key, level),
                "GET": ("MapGetOutputKey", "binder", level),
            }

def get_xtr_name_level_package_compositions(game, key, level):
    match game:
        case "Gks0":
            return {"XTR": ("Xtr", key, level)}
        case "Gks1" | "Gks0Map" | "GksMapXpd":
            return {"XTR": ("MapXtr", key, level)}

def get_hash_package_parameters(game):
    params = {}
    if game in GAMES_AFTER_IDEALIZATION:
        params["b"] = "true"
    if game in GAMES_BEFORE_IDEALIZATION:
        params["b"] = "false"
    return params

def generate_package_with_template(key, level, template_name, package_name):
    with open(os.path.join(PACKAGES_DIR, template_name)) as f:
        content = f.read()
    new_content = content.replace("Name", key).replace("Level", str(level))
    os.makedirs(os.path.join(PACKAGES_DIR, "autogenerated"), exist_ok=True)
    with open(os.path.join(PACKAGES_DIR, "autogenerated", package_name), "w") as f:
        f.write(new_content)

def generate_get_output_key_name_level_package(key, level):
    generate_package_with_template(key, level, "GetOutputKey_Name_Level.pkg.ssp", f"GetOutputKey_{key}_{level}.pkg.ssp")

def generate_xpd_name_level_package(key, level):
    generate_package_with_template(key, level, "Xpd_Name_Level.pkg.ssp", f"Xpd_{key}_{level}.pkg.ssp")

def generate_xtr_name_level_package(key, level):
    generate_package_with_template(key, level, "Xtr_Name_Level.pkg.ssp", f"Xtr_{key}_{level}.pkg.ssp")

def get_adversary_compositions(game):
    compositions = {}
    for (key, level) in itertools.product(OUTPUT_KEYS, range(LEVELS_COUNT)):
        compositions[f"GET_{key}_{level}"] = ("GetOutputKey_Name_Level", f"GetOutputKey_{key}_{level}", key, level)
    for (key, level) in itertools.product(XPD_KEYS, range(LEVELS_COUNT)):
        compositions[f"XPD_{key}_{level}"] = ("Xpd_Name_Level", f"Xpd_{key}_{level}", key, level)
    for (key, level) in itertools.product(XTR_KEYS, range(LEVELS_COUNT)):
        compositions[f"XTR_{key}_{level}"] = ("Xtr_Name_Level", f"Xtr_{key}_{level}", key, level)
    match game:
        case "Gks0":
            compositions["DHGEN"] = "DH"
            compositions["DHEXP"] = "DH"
            compositions["SET"] = ("Key", "psk", 0)
            return compositions
        case "Gks1" | "Gks0Map" | "GksMapXpd":
            compositions["DHGEN"] = "MapDH"
            compositions["DHEXP"] = "MapDH"
            compositions["SET"] = "MapPSK"
            return compositions

class ParameterExtractor(lark.visitors.Visitor_Recursive):
    def __init__(self):
        self.parameters = {}

    def decl_spec(self, decl):
        identifier, tipe = decl.children
        self.parameters[identifier.value] = (tipe.meta.start_pos, tipe.meta.end_pos)

def get_instance_type(instance):
    if isinstance(instance, str):
        return instance
    elif isinstance(instance, tuple):
        return instance[0]
    else:
        raise NotImplementedError(f"unknown package type {instance}")

def get_instance_name(instance):
    if isinstance(instance, str):
        return instance
    elif isinstance(instance, tuple):
        match instance:
            case (("GetOutputKey_Name_Level" | "Xpd_Name_Level" | "Xtr_Name_Level"), _, _, _):
                return instance[1]
            case _:
                return instance[0]
    else:
        raise NotImplementedError(f"unknown package type {instance}")

def instance_to_sorting_key(instance):
    if isinstance(instance, str):
        return (instance,)
    if isinstance(instance, tuple):
        return instance
    raise NotImplementedError(f"Unknown instance type {instance}")

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
        instances_parameters[instance] = {}
        match instance:
            case "adversary":
                instances_compositions[instance] = get_adversary_compositions(game)
            case "DH":
                instances_compositions[instance] = {
                    "SET": "NKey"
                }
            case "Hash":
                instances_parameters[instance] = get_hash_package_parameters(game)
                instances_compositions[instance] = {
                    "hash": "hash0"
                }
            case "NKey":
                instances_compositions[instance] = {
                    "UNQ": ("Log", "dh"),
                    "Q": ("Log", "dh")
                }
            case "MapDH":
                instances_compositions[instance] = {
                    "DHGEN": "DH",
                    "DHEXP": "DH",
                    "GETMAP": ("MapTable", "dh"),
                    "SETMAP": ("MapTable", "dh")
                }
            case "MapPSK":
                instances_compositions[instance] = {
                    "SETMAP": ("MapTable", "psk"),
                    "SET": ("Key", "psk", 0)
                }
            case ("MapGetOutputKey", key, level):
                instances_compositions[instance] = {
                    "GET": ("Key", key, level),
                    "GETMAP": ("MapTable", key, level)
                }
            case ("MapXtr", key, level):
                instances_parameters[instance] = {"n": KEYS.index(key)}
                instances_compositions[instance] = get_map_xtr_package_compositions(key, level)
            case ("MapXpd", key, level):
                instances_parameters[instance] = {"n": KEYS.index(key)}
                instances_compositions[instance] = get_map_xpd_package_compositions(key, level)
            case ("MapXpdOutputKeyInline", key, level):
                instances_parameters[instance] = {"n": KEYS.index(key)}
                instances_compositions[instance] = get_map_xpd_output_key_inline_package_compositions(key, level)
            case ("MapXpdOutputKeyRemap", key, level):
                instances_parameters[instance] = {"n": KEYS.index(key)}
                instances_compositions[instance] = get_map_xpd_output_key_remap_package_compositions(key, level)
            case ("KeyAdapter", key, level):
                match key:
                    case "0ikm" | "0salt":
                        instances_compositions[instance] = {
                            "GET": "ZKey"
                        }
                    case "dh":
                        instances_compositions[instance] = {
                            "GET": "NKey"
                        }
                    case _:
                        instances_compositions[instance] = {
                            "GET": ("Key", key, level)
                        }
            case ("MapAdapter", key, level):
                instances_compositions[instance] = {
                    "GETMAP": ("MapTable", key, level)
                }
            case ("Xpd", key, level):
                instances_parameters[instance] = get_xpd_package_parameters(key, level)
                instances_compositions[instance] = get_xpd_package_compositions(key, level)
            case ("Xtr", key, level):
                instances_parameters[instance] = get_xtr_package_parameters(game, key, level)
                instances_compositions[instance] = get_xtr_package_compositions(key, level)
            case ("Key", key, level):
                instances_parameters[instance] = get_key_package_parameters(game, key, level)
                instances_compositions[instance] = get_key_package_compositions(key)
            case ("Log", key):
                instances_parameters[instance] = get_log_package_parameters(game, key)
                instances_compositions[instance] = {}
            case ("GetOutputKey_Name_Level", _, key, level):
                instances_compositions[instance] = get_get_output_key_package_compositions(game, key, level)
            case ("Xpd_Name_Level", _, key, level):
                instances_compositions[instance] = {
                    "XPD": ("Check", key, level)
                }
            case ("Xtr_Name_Level", _, key, level):
                instances_compositions[instance] = get_xtr_name_level_package_compositions(game, key, level)
            case ("Check", key, level):
                instances_parameters[instance] = {
                    "n": KEYS.index(key),
                    "l": level
                }
                instances_compositions[instance] = get_check_package_compositions(game, key, level)
            case ("MapTable", _) | ("MapTable", _, _) | "ZKey" | "xtr0" | "xpd0" | "hash0" | "Labels" | "Sample":
                continue
            case p:
                raise NotImplementedError(f"Can not handle package {p}")
        for p in set(instances_compositions[instance].values()):
            stack.append(p)
    print("Constructed call graph")

    # extract abstract functions
    print("Extracting parameters")
    for instance in instances:
        package_type = get_instance_type(instance)
        match package_type:
            case "GetOutputKey_Name_Level" | "Xpd_Name_Level" | "Xtr_Name_Level":
                continue
            case _:
                package_parameters = instances_parameters[instance]
                for parameter, value in packages_parameters[package_type].items():
                    if parameter not in package_parameters:
                        package_parameters[parameter] = parameter
                        abstract_functions_signatures[parameter] = value
                        all_abstract_functions_signatures[parameter] = value
    game_abstract_functions_signatures[game] = abstract_functions_signatures.keys()
    print("Extracted parameters")

    # give concrete names to instances
    for instance in instances:
        instance_name = ["pkg"]
        if isinstance(instance, tuple):
            match instance:
                case (("GetOutputKey_Name_Level" | "Xpd_Name_Level" | "Xtr_Name_Level"), _, _, _):
                    instance_name.append(instance[0])
                    instance_name.append(instance[1])
                case _:
                    instance_name.extend(map(str, list(instance)))
        elif isinstance(instance, str):
            instance_name.append(instance)
        else:
            raise NotImplementedError(f"Can not handle name {instance}")
        instances_names[instance] = "_".join(instance_name)

    # generate Xpd_Name_Level, Xtr_Name_Level, GetOutputKey_Name_Level packages
    for (key, level) in itertools.product(OUTPUT_KEYS, range(LEVELS_COUNT)):
        generate_get_output_key_name_level_package(key, level)
    print("Generated GetOutputKey_Name_Level packages")

    for (key, level) in itertools.product(XPD_KEYS, range(LEVELS_COUNT)):
        generate_xpd_name_level_package(key, level)
    print("Generated Xpd_Name_Level packages")

    for (key, level) in itertools.product(XTR_KEYS, range(LEVELS_COUNT)):
        generate_xtr_name_level_package(key, level)
    print("Generated Xtr_Name_Level packages")

    # generate game files
    lines = [f"composition {game} {{\n"]
    for name, signature in sorted(abstract_functions_signatures.items()):
        lines.append(f"\tconst {name}: {signature};\n")
    lines.append("\n")
    for instance in sorted(instances, key=instance_to_sorting_key):
        package_type = get_instance_name(instance)
        lines.append(f"\tinstance {instances_names[instance]} = {package_type} {{\n")
        if len(instances_parameters[instance]) > 0:
            lines.append("\t\tparams {\n")
            for parameter, value in sorted(instances_parameters[instance].items()):
                lines.append(f"\t\t\t{parameter}: {value},\n")
            lines.append("\t\t}\n")
        lines.append("\t}\n")
        lines.append("\n")
    lines.append("\tcompose {\n")
    for instance, dependencies in sorted(
            instances_compositions.items(),
            key=lambda p: instance_to_sorting_key(p[0])):
        if len(dependencies) == 0:
            continue
        lines.append(f"\t\t{instances_names[instance]}: {{\n")
        for imported_oracle, imported_instance in sorted(dependencies.items(), key=operator.itemgetter(0)):
            lines.append(f"\t\t\t{imported_oracle}: {instances_names[imported_instance]},\n")
        lines.append(f"\t\t}},\n")
    lines.append("\t}\n")
    lines.append("}\n")

    with open(os.path.join(GAMES_DIR, f"{game}.comp.ssp"), "w") as f:
        f.writelines(lines)

# generate proof file
proof_lines = ["proof Proof {\n"]
for name, signature in sorted(all_abstract_functions_signatures.items()):
    proof_lines.append(f"\tconst {name}: {signature};\n")
proof_lines.append("\n")
for game in GAMES:
    proof_lines.append(f"\tinstance game_{game} = {game} {{\n")
    proof_lines.append("\t\tparams {\n")
    for name in sorted(game_abstract_functions_signatures[game]):
        proof_lines.append(f"\t\t\t{name}: {name},\n")
    proof_lines.append("\t\t}\n")
    proof_lines.append("\t}\n")
    proof_lines.append("\n")
proof_lines.append("}\n")

if not os.path.exists(PROOF_FILE_PATH):
    with open(PROOF_FILE_PATH, "w") as f:
        f.writelines(proof_lines)
else:
    os.makedirs(os.path.join(PROOF_DIR, "autogenerated"), exist_ok=True)
    with open(os.path.join(PROOF_DIR, "autogenerated", "proof.ssp"), "w") as f:
        f.writelines(proof_lines)