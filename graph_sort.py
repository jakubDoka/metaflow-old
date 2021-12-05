graph = [
    [1, 2],
    [6, 5],
    [3, 6],
    [1, 4],
    [5, 6],
    [6],
    [],
]

def depsort(graph, print_frontier = False):
    result = []
    frontier = [0]
    lookup = [None] * len(graph)
    i = 0
    while i < len(frontier):
        node = frontier[i]
        seen_at = lookup[node]
        if seen_at != None:
            result[seen_at] = None
        lookup[node] = len(result)
        result.append(node)
        frontier.extend([i for i in graph[node] if i != frontier[len(frontier) - 1]])
        i += 1

    return list(filter(lambda a: a != None, result))

def find_cycle(graph):
    stack = [[0, 0]]

    while len(stack) > 0:
        node, idx = stack[len(stack) - 1]
        if idx >= len(graph[node]):
            stack.pop()
        else:
            stack[len(stack) - 1][1] = idx + 1
            next = graph[node][idx]
            for i in range(len(stack) - 1, 0, -1):
                if stack[i][0] == next:
                    return True
            stack.append([next, 0])            
    return False

def find_cycle_2(graph, node = 0, stack = None, counter = 0):
    if stack == None: stack = []
    if node in stack:
        return True
    stack.append(node)
    for i in graph[node]:
        if find_cycle_2(graph, i, stack, counter + 1):
            return True
    stack.pop()
    return False

print(depsort(graph))
print(find_cycle_2(graph))

import random

for i in range(10000):
    length = 10
    graph = [None] * length
    for j in range(length - 1):
        graph[j] = [random.randrange(1, length) for _ in range(random.randrange(1, length))]
    graph[len(graph) - 1] = []
    
    assert find_cycle_2(graph) == find_cycle(graph), (i, graph)