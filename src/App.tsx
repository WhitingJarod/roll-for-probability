import React, { useEffect, useCallback, useState } from "react";
import {
  ReactFlow,
  useNodesState,
  useEdgesState,
  addEdge,
  MiniMap,
  Controls,
  type Connection,
} from "@xyflow/react";

import "@xyflow/react/dist/style.css";

import RenderNode from "./components/nodes/RenderNode";

import { loadWasm } from "./wasm-loader";
import type * as WasmModule from "../public/pkg/rust_code";

const snapGrid = [20, 20];
const nodeTypes = {
  renderNode: RenderNode,
};

const defaultViewport = { x: 0, y: 0, zoom: 1.5 };

import { type Node, type Edge } from "@xyflow/react";

const CustomNodeFlow = () => {
  // ALL HOOKS MUST BE AT THE TOP
  const [wasm, setWasm] = useState<typeof WasmModule | null>(null);
  const [nodes, setNodes, onNodesChange] = useNodesState([] as Node[]);
  const [edges, setEdges, onEdgesChange] = useEdgesState([] as Edge[]);

  useEffect(() => {
    loadWasm().then(setWasm);
  }, []);

  useEffect(() => {
    if (!wasm) return;

    setNodes([
      {
        id: "1",
        type: "input",
        data: { label: "An input node" },
        position: { x: 0, y: 50 },
        // sourcePosition: Position.Right,
      },
      {
        id: "2",
        type: "renderNode",
        data: {},
        position: { x: 300, y: 50 },
        // targetPosition: Position.Left,
      },
    ]);

    // setEdges([
    //   {
    //     id: "e1-2",
    //     source: "1",
    //     target: "2",
    //     animated: true,
    //   },
    // ]);
  }, [wasm]);

  const getNodeById = useCallback(
    (id: string) => {
      const node = nodes.find((node) => node.id === id);
      if (node === undefined) {
        throw new Error(`Node with id "${id}" not found.`);
      }
      return node;
    },
    [nodes]
  );

  const onConnect = useCallback(
    (params: Connection) => {
      setEdges((eds) => addEdge({ ...params, animated: true }, eds));
      const target = getNodeById(params.target);
      console.log(target.domAttributes);
    },
    [getNodeById]
  );

  // Early return AFTER all hooks
  if (!wasm) {
    return <div>Loading WASM...</div>;
  }

  return (
    <ReactFlow
      nodes={nodes}
      edges={edges}
      onNodesChange={onNodesChange}
      onEdgesChange={onEdgesChange}
      onConnect={onConnect}
      style={{ background: "#70F" }}
      nodeTypes={nodeTypes}
      snapToGrid={true}
      snapGrid={snapGrid as [number, number]}
      defaultViewport={defaultViewport}
      fitView
      attributionPosition="bottom-left"
    >
      {/* <MiniMap
        nodeStrokeColor={(n) => {
          if (n.type === "input") return "#0041d0";
          if (n.type === "renderNode") return "#ff0072";
          return "#f0f";
        }}
        nodeColor={(_n) => {
          return "#fff";
        }}
      /> */}
      <Controls />
    </ReactFlow>
  );
};

export default CustomNodeFlow;
