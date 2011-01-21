#!/usr/bin/env python
# -*- coding:utf-8 -*-

import sys
import getopt
import re
import random


def gen_labeled_graph(node_size):
    graph = []
    for m in xrange(node_size):
        graph.append([])
        for n in xrange(node_size):
            graph[m].append([])
    return graph

def gen_random_graph(node_size, label_size, gen_edge_rate):
    graph = gen_labeled_graph(node_size)
    for m in graph:
        for n in m:
            for i in xrange(label_size):
                if (gen_edge_rate >= random.random()):
                    n.append(i)
    return graph

def get_label(graph):
    label = []
    for m in graph:
        for n in m:
            for c in n:
                if c not in label:
                    label.append(c)
    return label



def _get_terminate_node(graph, terminate_node=None):
    if (terminate_node == None):
        terminate_node = []
    node_size = len(graph)
    num = 0
    for i in xrange(node_size):
        if (i not in terminate_node):
            has_edge = False
            for j in xrange(node_size):
                if (j not in terminate_node and len(graph[i][j]) > 0):
                    has_edge = True
            if (not has_edge):
                terminate_node.append(i)
                num = num + 1
    if (num > 0):
        terminate_node = _get_terminate_node(graph, terminate_node)
    return terminate_node

def gen_nonterminate_graph(graph, node_map=None):
    node_size = len(graph)
    terminate_node = _get_terminate_node(graph)
    nonterminate_node_size = node_size - len(terminate_node)
    nonterminate_graph = gen_labeled_graph(nonterminate_node_size)
    if (node_map == None):
        node_map = [0] * node_size
    I = 0
    for i in xrange(node_size):
        if (i not in terminate_node):
            J = 0
            for j in xrange(node_size):
                if (j not in terminate_node):
                    for k in graph[i][j]:
                        nonterminate_graph[I][J].append(k)
                    J = J + 1
            node_map[i] = I
            I = I + 1
    return nonterminate_graph



def _has_same_labeled_path(terminal_node1, terminal_node2, graph):
    node_size = len(graph)
    for m in graph:
        for i in m[terminal_node1]:
            if (i in m[terminal_node2]):
                return True
    return False

def _make_node_table_of_right_resolving_graph(graph):
    node_size = len(graph)
    node_table_size = node_size - 1
    node_table = []
    for i in xrange(node_table_size):
        node_table.append([0] * (node_table_size - i))
        for j in xrange(node_table_size - i):
            if (_has_same_labeled_path(i, i + j + 1, graph)):
                node_table[i][j] = 1
    return node_table

def _make_subset_node_map(node_table):
    node_table_size = len(node_table)
    node_size = node_table_size + 1
    node_map = [-1] * node_size
    codomain_size = 0
    for i in xrange(node_table_size):
        if (node_map[i] == -1):
            node_map[i] = codomain_size
            for j in xrange(node_table_size - i):
                if (node_table[i][j]):
                    node_map[i + j + 1] = codomain_size
            codomain_size = codomain_size + 1
    if (node_map[node_table_size] == -1):
        node_map[node_table_size] = codomain_size
        codomain_size = codomain_size + 1
    return node_map, codomain_size

def _get_subset_node(node_size, node_list, node_map, cardinal_number):
    index = None
    for i in node_list:
        if (index == None):
            index = node_map[i]
        elif (index != node_map[i]):
            index = None
            break
    subset_node = -1
    n = 0
    for i in xrange(node_size):
        if (node_map[i] == index):
            if (i in node_list):
                subset_node = subset_node + pow(2, n)
            n = n + 1
    if (index != None):
        for i in xrange(index):
            subset_node = subset_node + cardinal_number[i];
    return subset_node

def _get_node_list(node_size, subset_node, node_map, cardinal_number):
    index = 0
    while (subset_node >= cardinal_number[index]):
        subset_node = subset_node - cardinal_number[index]
        index = index + 1
    subset_node = subset_node + 1
    node_list = []
    for i in xrange(node_size):
        if (node_map[i] == index):
            if (subset_node % 2 > 0):
                node_list.append(i)
                subset_node = subset_node - 1
            subset_node = subset_node / 2
    return node_list

def _get_terminal_subset_node(initial_subset_node, label, graph, node_map,
        cardinal_number):
    node_size = len(graph)
    initial_node_list = _get_node_list(node_size, initial_subset_node,
            node_map, cardinal_number)
    terminal_node_list = []
    for i in initial_node_list:
        for j in xrange(node_size):
            if (label in graph[i][j]):
                terminal_node_list.append(j)
    return _get_subset_node(node_size, terminal_node_list, node_map,
            cardinal_number)

def gen_right_resolving_graph(graph):
    if len(graph) == 0:
        return graph
    node_table = _make_node_table_of_right_resolving_graph(graph)
    node_map, codomain_size = _make_subset_node_map(node_table)
    cardinal_number = [0] * codomain_size
    right_resolving_node_size = 0
    for i in xrange(codomain_size):
        n = node_map.count(i)
        cardinal_number[i] = pow(2, n) - 1
        right_resolving_node_size = (right_resolving_node_size +
                cardinal_number[i])
    right_resolving_graph = gen_labeled_graph(right_resolving_node_size)
    label = get_label(graph)
    for i in xrange(right_resolving_node_size):
        subset_node = {}
        for j in label:
            subset_node[j] = _get_terminal_subset_node(i, j, graph, node_map,
                    cardinal_number)
        for j in label:
            n = subset_node[j]
            if (n != -1):
                for k in label:
                    if (n == subset_node[k]):
                        right_resolving_graph[i][n].append(k)
                        subset_node[k] = -1
    return right_resolving_graph



def _get_terminal_node(graph, initial_node, label):
    for i in xrange(len(graph)):
        if (label in graph[initial_node][i]):
            return i
    return None

def _marking(node_table, indexI, indexJ, pair):
    node_table_size = len(node_table)
    if ('X' not in node_table[indexI][indexJ]):
        node_table[indexI][indexJ] = ['X']
        for i in xrange(node_table_size):
            for j in xrange(node_table_size - i):
                if (pair[indexI][indexJ] in node_table[indexI][indexJ]):
                    _marking(node_table, i, j, pair)

def _make_node_table_of_minimal_graph(graph): 
    node_size = len(graph)
    node_table_size = node_size - 1
    label = get_label(graph)
    node_table = []
    pair = []
    for i in xrange(node_table_size):
        node_table.append([])
        pair.append([])
        for j in xrange(node_table_size - i):
            node_table[i].append([])
            pair[i].append(j)
    for i in xrange(node_table_size):
        for j in xrange(node_table_size - i):
            for k in label:
                I = _get_terminal_node(graph, i, k)
                J = _get_terminal_node(graph, i + j + 1, k)
                if ((I == None and J != None) or (I != None and J == None)):
                    node_table[i][j] = []
                    _marking(node_table, i, j, pair)
                elif (I != J):
                    if (I > J):
                        tmp = I
                        I = J
                        J = tmp
                    if ('X' in node_table[I][J-I-1]):
                        node_table[i][j] = []
                        _marking(node_table, i, j, pair)
                    else:
                        node_table[i][j].append(pair[I][J-I-1])
    return node_table

def _make_merged_node_map(node_table):
    node_table_size = len(node_table)
    node_size = node_table_size + 1
    node_map = [-1] * node_size
    codomain_size = 0
    for i in xrange(node_table_size):
        if (node_map[i] == -1):
            node_map[i] = codomain_size
            for j in xrange(node_table_size - i):
                if ('X' not in node_table[i][j]):
                    node_map[i + j + 1] = codomain_size
            codomain_size = codomain_size + 1
    if (node_map[node_table_size] == -1):
        node_map[node_table_size] = codomain_size
        codomain_size = codomain_size + 1
    return node_map, codomain_size

def gen_minimal_graph(graph, node_map=None):
    if len(graph) == 0:
        return graph
    node_size = len(graph)
    node_table = _make_node_table_of_minimal_graph(graph)
    merged_node_map, minimal_node_size = _make_merged_node_map(node_table)
    if (node_map == None):
        node_map = merged_node_map
    else:
        for i in xrange(node_size):
            node_map[i] = merged_node_map[i]
    minimal_graph = gen_labeled_graph(minimal_node_size)
    for I in xrange(minimal_node_size):
        for J in xrange(minimal_node_size):
            label = []
            for i in xrange(node_size):
                if (node_map[i] == I):
                    for j in xrange(node_size):
                        if (node_map[j] == J):
                            for k in graph[i][j]:
                                if (k not in label):
                                    label.append(k)
            for i in label:
                minimal_graph[I][J].append(i)
    return minimal_graph


def _add_edge_in_labeled_graph(initial_node, terminal_node, label, graph,
        edge_count, node_count):
    if (label not in graph[initial_node][terminal_node]):
        graph[initial_node][terminal_node].append(label)
    if (not edge_count[initial_node][terminal_node].has_key(label)):
        edge_count[initial_node][terminal_node][label] = 0
    edge_count[initial_node][terminal_node][label] = \
            (edge_count[initial_node][terminal_node][label] + 1)
    node_count[terminal_node] = node_count[terminal_node] + 1

def _extend_node_size(graph, edge_count, node_count):
    graph.append([])
    edge_count.append([])
    node_size = len(graph)
    for i in xrange(node_size-1):
        graph[i].append([])
        edge_count[i].append({})
    for i in xrange(node_size):
        graph[node_size-1].append([])
        edge_count[node_size-1].append({})
    node_count.append(0)
    return node_size

def _add_sequence_in_labeled_graph(sequence, block_length,
        graph=None,edge_count=None, node_count=None):
    if graph == None:
        graph = gen_labeled_graph(0)
    node_size = len(graph)
    if edge_count == None:
        edge_count = []
        for i in xrange(node_size):
            edge_count.append([])
            for j in xrange(node_size):
                edge_count[i].append({})
                for k in graph[i][j]:
                    edge_count[i][j][k] = 0
    if node_count == None:
        node_count = [0] * node_size
    tree = []
    initial_node = None
    for n in xrange(len(sequence) - block_length + 1):
        block = tuple(sequence[n:n+block_length])
        if block not in tree:
            tree.append(block)
            _extend_node_size(graph, edge_count, node_count)
        terminal_node = tree.index(block)
        if (initial_node != None):
            _add_edge_in_labeled_graph(initial_node, terminal_node,
                    block[block_length-1], graph, edge_count, node_count)
        initial_node = terminal_node
    return graph, edge_count, node_count

def gen_labeled_graph_from_sequence(sequence, block_length):
    if (len(sequence) > 0 and isinstance(sequence[0], list)):
        graph, edge_count, node_count = None, None, None
        for s in sequence:
            graph, edge_count, node_count = _add_sequence_in_labeled_graph(s,
                    block_length, graph, edge_count, node_count)
        return graph, edge_count, node_count
    else:
        return _add_sequence_in_labeled_graph(sequence, block_length)


def remove_edge_from_labeled_graph(graph, edge_count, threshold):
    node_size = len(graph)
    for i in xrange(node_size):
        sum = 0
        for j in xrange(node_size):
            for k, n in edge_count[i][j].iteritems():
                sum = sum + n
        for j in xrange(node_size):
            label = [x for x in graph[i][j]]
            for k in label:
                p = edge_count[i][j][k]/float(sum)
                if (p <= threshold):
                    edge_count[i][j].pop(k)
                    graph[i][j].remove(k)


def convert_trans_count(graph, conv_graph, node_map, edge_count, node_count):
    node_size = len(graph)
    conv_node_size = len(conv_graph)
    conv_edge_count = []
    for i in xrange(conv_node_size):
        conv_edge_count.append([])
        for j in xrange(conv_node_size):
            conv_edge_count[i].append({})
            for k in conv_graph[i][j]:
                conv_edge_count[i][j][k] = 0
    conv_node_count = [0] * conv_node_size
    for i in xrange(node_size):
        I = node_map[i]
        for j in xrange(node_size):
            J = node_map[j]
            for k in graph[i][j]:
                if (k in conv_graph[I][J]):
                    conv_edge_count[I][J][k] = (conv_edge_count[I][J][k] +
                            edge_count[i][j][k])
        conv_node_count[I] = conv_node_count[I] + node_count[i]
    return conv_edge_count, conv_node_count



def print_labeled_graph(graph):
    node_size = len(graph)
    print "digraph mygraph{"
    for i in xrange(node_size):
        for j in xrange(node_size):
            for k in graph[i][j]:
                print '"%d" -> "%d" [label="%s"]' % (i, j, k)
    print "}"

def print_labeled_graph_with_count(graph, edge_count):
    node_size = len(graph)
    print "digraph mygraph{"
    for i in xrange(node_size):
        for j in xrange(node_size):
            for k in graph[i][j]:
                print '"%d" -> "%d" [label="%s(%d)"]' % (i, j, k,
                        edge_count[i][j][k])
    print "}"

def print_labeled_graph_with_frequency(graph, edge_count):
    node_size = len(graph)
    print "digraph mygraph{"
    for i in xrange(node_size):
        sum = 0
        for j in xrange(node_size):
            for k, n in edge_count[i][j].iteritems():
                sum = sum + n
        for j in xrange(node_size):
            for k in graph[i][j]:
                print '"%d" -> "%d" [label="%s(%f)"]' % (i, j, k,
                        edge_count[i][j][k]/float(sum))
    print "}"


def main():
    block_length = 2
    try:
        opts, args = getopt.getopt(sys.argv[1:], "n:")
    except getopt.GetoptError:
        print "Usage: %s [-n block-length] file ..." % sys.argv[0]
        sys.exit(0)
    for opt, arg in opts:
        if opt in ("-n"):
            block_length = int(arg)
    if len(args) == 0:
        print "Usage: %s [-n block-length] file ..." % sys.argv[0]
        sys.exit(0)

    s_list = []
    p = re.compile(r'(^#)|(^$)')
    for file in args:
        s = []
        s_list.append(s)
        for line in open(file, 'r'):
            if (p.match(line) == None):
                input = line[:-1].split()
                s.append(input[0])
    if s_list != []:
        graph, edge_count, node_count = \
                gen_labeled_graph_from_sequence(s_list, block_length)
        node_map = [0] * len(graph)
        minimal_graph = gen_minimal_graph(graph, node_map)
        edge_count, node_count = convert_trans_count(graph, minimal_graph,
                node_map, edge_count, node_count)
        print_labeled_graph_with_frequency(minimal_graph, edge_count)

if __name__ == "__main__":
    main()

