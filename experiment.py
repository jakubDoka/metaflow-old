modules = [
    (
        "deeper_module",
        [],
        [
            ("f", []),
        ]
    ),
    (
        "some_module",
        [
            "deeper_module",
        ],
        [
            (
                "a",
                [
                    "b",
                    "c",
                ]
            ),
            (
                "b",
                [
                    "c",
                    "f",
                ],
            ),
            ("c", [])
        ]
    ),
    (
        "some_other_module",
        [],
        [
            ("d", [])
        ]
    ),
    (
        "main",
        [
            "some_module",
            "some_other_module",
        ],
        [
            (
                "main",
                [
                    "a",
                    "d",
                ]
            )
        ]
    )
]

def find_module(name, sources):
    return next(i for i, s in enumerate(sources) if s[0] == name)

def build_module_tree(root, sources):
    module_tree = [None] * len(sources)
    root_module = find_module(root, sources)
    frontier = [root_module]
    while len(frontier) != 0:
        current = frontier.pop()
        deps = [d for d in map(lambda e: find_module(e, sources), sources[current][1])]
        module_tree[current] = deps
        frontier.extend(deps)
    return (module_tree, root_module)

(module_tree, root_module) = build_module_tree("main", modules)


for i in module_tree: print(i)

def find_function(module, name, module_tree, sources):
    found = [i for i, f in enumerate(sources[module][2]) if f[0] == name]
    
    if len(found) != 0:
        return (module, found[0])
    
    for dep in module_tree[module]:
        found = [i for i, f in enumerate(sources[dep][2]) if f[0] == name]
        if len(found) != 0:
            return (dep, found[0])
    
    return None

def build_function_tree(root, module_tree, sources):
    function_tree = {}
    frontier = [(root, 0)]
    while len(frontier) != 0:
        (current, current_index) = frontier[len(frontier) - 1]
        module = sources[current]
        function = module[2][current_index]
        deps = [d for d in map(lambda e: find_function(current, e, module_tree, sources), function[1])]
        function_tree[(current, current_index)] = deps
        current_index += 1
        if current_index == len(module[2]):
            frontier.pop()
        else:
            frontier[len(frontier) - 1] = (current, current_index)
        frontier.extend(deps)

    return function_tree

function_tree = build_function_tree(root_module, module_tree, modules)

for i in function_tree: print(i, function_tree[i])