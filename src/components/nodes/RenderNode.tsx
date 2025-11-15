import React, { memo, useRef, useEffect } from "react";
import { Handle, Position } from "@xyflow/react";

const RenderNode = memo(({ data }: { data: any }) => {
  const canvasRef = useRef<HTMLCanvasElement>(null);

  useEffect(() => {
    // Expose the render method to parent via data.setRenderFn
    if (data?.setRenderFn && canvasRef.current) {
      data.setRenderFn((renderLogic: (canvas: HTMLCanvasElement) => void) => {
        if (canvasRef.current) {
          renderLogic(canvasRef.current);
        }
      });
    }
  }, [data]);

  return (
    <>
      <Handle type="target" position={Position.Left} isConnectable={true} />
      <div>
        <canvas ref={canvasRef} width={200} height={200}></canvas>
      </div>
    </>
  );
});

export default RenderNode;
