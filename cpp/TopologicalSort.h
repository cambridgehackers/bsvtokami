//
// Imported by Jamey Hicks on 1/27/20.
// https://www.geeksforgeeks.org/topological-sorting/
//

#ifndef BSV_PARSER_TOPOLOGICALSORT_H
#define BSV_PARSER_TOPOLOGICALSORT_H

// A C++ program to print topological sorting of a DAG
#include<iostream>
#include <list>
#include <stack>
using namespace std;

// Class to represent a graph
class Graph
{
    int V; // No. of vertices'

    // Pointer to an array containing adjacency listsList
    list<int> *adj;

    // A function used by topologicalSort
    void topologicalSortUtil(int v, bool visited[], stack<int> &Stack);
public:
    Graph(int V); // Constructor
    ~Graph();

    // function to add an edge to graph
    void addEdge(int v, int w);

    // prints a Topological Sort of the complete graph
    void topologicalSort();
};




#endif //BSV_PARSER_TOPOLOGICALSORT_H
