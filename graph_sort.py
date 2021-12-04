graph = [
    [1, 2],
    [6, 5],
    [3, 6],
    [1, 4],
    [5, 6],
    [3],
    [],
]

def depsort(graph, print_frontier = False):
    result = []
    frontier = [0, None]
    lookup = [(None, 0)] * len(graph)
    i = 0
    current_level = 0
    while i < len(frontier):
        node = frontier[i]
        if node == None:
            if i == len(frontier) - 1:
                break
            frontier.append(None)
            current_level += 1
            i += 1
            continue
        seen, level = lookup[node]
        if seen != None:
            result[seen] = None
        else:
            level = current_level     
        lookup[node] = (len(result), level)
        result.append(node)
        dependency = graph[node]
        for j in dependency:
            dep_seen, dep_level = lookup[j]
            if j == node:
                return None
            if dep_seen != None and\
                (dep_level < level or\
                (dep_level == level and\
                node in graph[j])):
                return None
            if j == frontier[len(frontier) - 1]:
                continue           
            frontier.append(j)
        i += 1
        if print_frontier: print(frontier, node)
    return list(filter(lambda a: a != None, result))

def depsort_2(graph, node = 0, stack = None, counter = 0):
    if stack == None: stack = []
    if node in stack:
        return True
    stack.append(node)
    for i in graph[node]:
        if depsort_2(graph, i, stack, counter + 1):
            return True
    stack.pop()
    return False

print(depsort(graph))
print(depsort_2(graph))

import random

for i in range(10000):
    length = 10
    graph = [None] * length
    for j in range(length - 1):
        graph[j] = [random.randrange(1, length) for _ in range(random.randrange(1, length))]
    graph[len(graph) - 1] = []
    
    if depsort_2(graph) != (depsort(graph) == None):
        print(graph, depsort_2(graph), depsort(graph, True))
        break