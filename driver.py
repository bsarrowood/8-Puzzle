# created by:		Brad Arrowood
# created on:		2020.03.12
# last updated:     2020.04.21
# python version:   3.7.6
# run format:       python3 driver.py <method> <board>
# file:     		driver.py
# addendums:        state.py
# notes:    		8-puzzle solver using BFS, DFS, and A* algorithms

"""
When executed, your program will create / write to a file called output.txt, containing the following statistics:
 --path_to_goal: the sequence of moves taken to reach the goal
 --cost_of_path: the number of moves taken to reach the goal
 --nodes_expanded: the number of nodes that have been expanded
 --search_depth: the depth within the search tree when the goal node is found
 --max_search_depth:  the maximum depth of the search tree in the lifetime of the algorithm
 --running_time: the total running time of the search instance, reported in seconds
 --max_ram_usage: the maximum RAM usage in the lifetime of the process as measured by the ru_maxrss attribute in the resource module, reported in megabytes
"""

import argparse
import itertools
import timeit
import resource
import sys
from collections import deque
from datetime import datetime
from heapq import heappush, heappop, heapify
from state import PuzzleState

board_len = 0
board_side = 0
costs = set()
goal_node = PuzzleState
goal_state = [0, 1, 2, 3, 4, 5, 6, 7, 8]
initial_state = list()
max_frontier_size = 0
max_search_depth = 0
moves = list()
nodes_expanded = 0


def bfs(begin_state):
    # bfs was actually fun coding and after doing my city2city.py
    # it made this much easier to think through
    global goal_node
    global max_frontier_size
    global max_search_depth
    
    checked = set()
    queue = deque([PuzzleState(begin_state, None, None, 0, 0, 0)])

    while queue:
        node = queue.popleft()
        checked.add(node.map)
        if node.state == goal_state:
            goal_node = node
            return queue

        neighbors = expand(node)

        for neighbor in neighbors:
            if neighbor.map not in checked:
                queue.append(neighbor)
                checked.add(neighbor.map)
                if neighbor.depth > max_search_depth:
                    max_search_depth += 1

        if len(queue) > max_frontier_size:
            max_frontier_size = len(queue)

def dfs(begin_state):
    # oddly enough dfs is fairly similar to bfs with some adjustments
    # while remembering the differences in how they operate is one thing
    # coding them felt pretty similar especially after doing my city2city.py
    global goal_node
    global max_frontier_size
    global max_search_depth
    
    checked = set()
    stack = list([PuzzleState(begin_state, None, None, 0, 0, 0)])
    
    while stack:
        node = stack.pop()
        checked.add(node.map)
        if node.state == goal_state:
            goal_node = node
            return stack

        neighbors = reversed(expand(node))

        for neighbor in neighbors:
            if neighbor.map not in checked:
                stack.append(neighbor)
                checked.add(neighbor.map)
                if neighbor.depth > max_search_depth:
                    max_search_depth += 1

        if len(stack) > max_frontier_size:
            max_frontier_size = len(stack)

def ast(begin_state):
    # while a* may be a great algorithm this was a pain piecing together
    global goal_node
    global max_frontier_size
    global max_search_depth
    
    checked = set()
    heap = list()
    heap_entry = {}
    counter = itertools.count()
    key = holding(begin_state)
    root = PuzzleState(begin_state, None, None, 0, 0, key)
    entry = (key, 0, root)
    heappush(heap, entry)
    heap_entry[root.map] = entry

    while heap:
        node = heappop(heap)
        checked.add(node[2].map)
        if node[2].state == goal_state:
            goal_node = node[2]
            return heap

        neighbors = expand(node[2])

        for neighbor in neighbors:
            neighbor.key = neighbor.cost + holding(neighbor.state)
            entry = (neighbor.key, neighbor.move, neighbor)
            if neighbor.map not in checked:
                heappush(heap, entry)
                checked.add(neighbor.map)
                heap_entry[neighbor.map] = entry
                if neighbor.depth > max_search_depth:
                    max_search_depth += 1
            elif neighbor.map in heap_entry and neighbor.key < heap_entry[neighbor.map][2].key:
                hindex = heap.index((heap_entry[neighbor.map][2].key,
                                     heap_entry[neighbor.map][2].move,
                                     heap_entry[neighbor.map][2]))
                heap[int(hindex)] = entry
                heap_entry[neighbor.map] = entry
                heapify(heap)
        if len(heap) > max_frontier_size:
            max_frontier_size = len(heap)

def holding(state):
    return sum(abs(b % board_side - g % board_side) + abs(b//board_side - g//board_side)
               for b, g in ((state.index(i), goal_state.index(i)) for i in range(1, board_len)))

def expand(node):
    global nodes_expanded

    nodes_expanded += 1
    neighbors = list()

    neighbors.append(PuzzleState(move(node.state, 1), node, 1, node.depth + 1, node.cost + 1, 0))
    neighbors.append(PuzzleState(move(node.state, 2), node, 2, node.depth + 1, node.cost + 1, 0))
    neighbors.append(PuzzleState(move(node.state, 3), node, 3, node.depth + 1, node.cost + 1, 0))
    neighbors.append(PuzzleState(move(node.state, 4), node, 4, node.depth + 1, node.cost + 1, 0))
    nodes = [neighbor for neighbor in neighbors if neighbor.state]

    return nodes

def move(state, position):
    # pretty self explanitory, doing the moves and returning the new state to work with
    new_state = state[:]
    index = new_state.index(0)

    if position == 1:  # Up
        if index not in range(0, board_side):
            temp = new_state[index - board_side]
            new_state[index - board_side] = new_state[index]
            new_state[index] = temp

            return new_state
        else:
            return None

    if position == 2:  # Down
        if index not in range(board_len - board_side, board_len):
            temp = new_state[index + board_side]
            new_state[index + board_side] = new_state[index]
            new_state[index] = temp

            return new_state
        else:
            return None

    if position == 3:  # Left
        if index not in range(0, board_len, board_side):
            temp = new_state[index - 1]
            new_state[index - 1] = new_state[index]
            new_state[index] = temp

            return new_state
        else:
            return None

    if position == 4:  # Right
        if index not in range(board_side - 1, board_len, board_side):
            temp = new_state[index + 1]
            new_state[index + 1] = new_state[index]
            new_state[index] = temp

            return new_state
        else:
            return None

def export(frontier, timeit):
    global moves
    
    moves = backtrace()

    file = open('output.txt', 'w')
    file.write("path_to_goal: " + str(moves))
    file.write("\ncost_of_path: " + str(len(moves)))
    file.write("\nnodes_expanded: " + str(nodes_expanded))
    file.write("\nfringe_size: " + str(len(frontier)))
    file.write("\nmax_fringe_size: " + str(max_frontier_size))
    file.write("\nsearch_depth: " + str(goal_node.depth))
    file.write("\nmax_search_depth: " + str(max_search_depth))
    file.write("\nrunning_time: " + format(timeit, '.8f'))
    file.write("\nmax_ram_usage: " + format(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1000.0, '.8f'))    
    file.close()

def backtrace():
    current_node = goal_node

    while initial_state != current_node.state:
        if current_node.move == 1:
            movement = 'Up'
        elif current_node.move == 2:
            movement = 'Down'
        elif current_node.move == 3:
            movement = 'Left'
        else:
            movement = 'Right'

        moves.insert(0, movement)
        current_node = current_node.parent

    return moves

def read(configuration):
    global board_len
    global board_side
    
    data = configuration.split(",")
    
    for element in data:
        initial_state.append(int(element))

    board_len = len(initial_state)
    board_side = int(board_len ** 0.5)

function_map = {
    # quick and easy for working with each algorithm choice
    'bfs': bfs,
    'dfs': dfs,
    'ast': ast
}

def board(begin_state,formula):
    # made this to draw the start board for a visual compare to goal state
    print("")
    goalR1 = "   0 1 2"
    goalR2 = "-> 3 4 5"
    goalR3 = "   6 7 8"
        
    board = [[begin_state[0],begin_state[1],begin_state[2],goalR1],
             [begin_state[3],begin_state[4],begin_state[5],goalR2],
             [begin_state[6], begin_state[7],begin_state[8],goalR3]]
        
    algorithm_used = formula.upper()
    
    print("Start    Goal")
    print('\n'.join(' '.join(map(str, x)) for x in board))
    print(f'\nCalculating solution using {algorithm_used}....\n')

def main():
    # here we're pulling out the type of algorithm we're going to be using
    # along with defining the board from the numbers entered separated by commas
    formula = sys.argv[1].lower()
    begin_state = sys.argv[2].split(",")
    begin_state = tuple(map(int, begin_state))
    board(begin_state,formula)
    
    # grabbing more info from the input, including timing the process
    # all requested info will be output to a file
    parser = argparse.ArgumentParser()
    parser.add_argument('algorithm')
    parser.add_argument('board')
    args = parser.parse_args()
    read(args.board)
    function = function_map[args.algorithm]
    start = timeit.default_timer()
    frontier = function(initial_state)
    stop = timeit.default_timer()
    export(frontier, stop-start)

if __name__ == '__main__':
    # start by running the main func
    # and ending with a printout to confirm script completed and output results
    main()
    print('Script completed. Check output.txt for the results.\n')