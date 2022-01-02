class Call:
    def __init__(self, id):
        self.id = id
    
    def __str__(self):
        return f"function{self.id}()"

class Function:
    def __init__(self, id, calls):
        self.id = id
        self.calls = calls
    
    def __str__(self):
        body = '\n  '.join(map(str, self.calls))
        return "fun function" + str(self.id) + "():\n  " + body + "\n"

class File:
    def __init__(self, range, path, dependency, functions):
        self.range = range
        self.path = path
        self.dependency = dependency
        self.functions = functions
    
    def __str__(self):
        imports = ("use\n  " + '\n  '.join(map(lambda i: f'"{i}"',self.dependency)) 
            if self.dependency else '') + "\n"
        return f"{imports}{''.join(map(str, self.functions))}"

import random

files = []

function_counter = 0
for i in range(100):
    path = f"root/module{i}.mf"
    range_start = function_counter
    function_count = random.randint(500, 1000)
    range_end = function_counter + function_count
    functions = []
    imports = set()
    for j in range(function_count):
        call_count = random.randint(5, 50)
        calls = []
        for k in range(call_count):
            call = random.randrange(range_end)
            for file in files:
                if call >= file.range[0] and call < file.range[1]:
                    imports.add(file.path)
                    break
            calls.append(Call(call))
        functions.append(Function(function_counter, calls))
        function_counter += 1
    files.append(File((range_start, range_end), path, list(imports), functions)) 

import os

for file in files:
    os.remove(file.path)
    f = open(file.path, 'x')
    f.write(str(file))