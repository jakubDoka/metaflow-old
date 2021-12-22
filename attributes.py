data = [
    ["push", 1, 2, 3],
    4,
    "element1",
    7,
    "element2",
    ["pop"],
    "element3",
]

marker = 0
collected = []
results = []
stack = []
frames = []
ordering = []

for element in data:
    if isinstance(element, list):
        if element[0] == "push":
            frames.append(len(stack))
            stack.extend(element[1:])
        elif element[0] == "pop":
            frame = frames.pop()
            stack = stack[:frame]
    elif isinstance(element, int):
        ordering.append(element)
    elif isinstance(element, str):
        ordering.extend(stack)
        results.append((element, marker, len(ordering)))
        marker = len(ordering)

for result in results:
    print(result[0], ordering[result[1]:result[2]])