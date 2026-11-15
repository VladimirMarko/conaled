#!/usr/bin/env python3
"""Render finite labelled action JSON as deterministic SVG using the standard library.

The renderer preserves edge rows. Coordinates and typography carry no algebraic
meaning and are not certified by the Lean edge-correspondence theorem.
"""
import argparse
import json
import math
from pathlib import Path
import xml.etree.ElementTree as ET

NS = "http://www.w3.org/2000/svg"
ET.register_namespace("", NS)
COLORS = ("#176b9b", "#ad3b43", "#88621b", "#663c9e")


def element(parent, tag, text=None, **attrs):
    node = ET.SubElement(parent, f"{{{NS}}}{tag}",
                         {k.replace("_", "-"): str(v) for k, v in attrs.items()})
    node.text = text
    return node


def point(x, y):
    return f"{x:.2f},{y:.2f}"


def offset(p, direction, radius=20):
    length = math.hypot(*direction)
    return (p[0] + radius * direction[0] / length,
            p[1] + radius * direction[1] / length)


def validate(diagram):
    vertices = diagram["vertices"]
    generators = diagram["generators"]
    edges = diagram["edges"]
    vids = [v["id"] for v in vertices]
    gids = [g["id"] for g in generators]
    if len(set(vids)) != len(vids) or len(set(gids)) != len(gids):
        raise ValueError("vertex and generator IDs must be unique")
    labels = {g["id"]: g["label"] for g in generators}
    ids = set()
    for edge in edges:
        if edge["id"] in ids:
            raise ValueError("edge IDs must be unique")
        ids.add(edge["id"])
        if edge["source"] not in vids or edge["target"] not in vids:
            raise ValueError("edge endpoint has no vertex")
        if edge["generator"] not in labels or labels[edge["generator"]] != edge["label"]:
            raise ValueError("edge label must match its generator")


def render(diagrams):
    root = ET.Element(f"{{{NS}}}svg", {
        "viewBox": f"0 0 {max(1, len(diagrams)) * 420} 600",
        "role": "img", "aria-labelledby": "title description",
        "font-family": "sans-serif", "font-size": "15",
    })
    element(root, "title", "Finite labelled action diagrams", id="title")
    element(root, "desc", "Directed generator edges, with separate indices for repeated labels.",
            id="description")
    element(root, "rect", width="100%", height="100%", fill="#f6f8fa")
    element(root, "text", "Finite labelled action diagrams", x=24, y=34,
            font_size=24, font_weight="bold", fill="#192c3b")
    element(root, "text", "Left actions · Arrowheads show direction · Generator indices remain distinct",
            x=24, y=60, fill="#435463")
    defs = element(root, "defs")
    for i, color in enumerate(COLORS):
        marker = element(defs, "marker", id=f"arrow{i}", viewBox="0 0 10 10",
                         refX=9, refY=5, markerWidth=6, markerHeight=6, orient="auto")
        element(marker, "path", d="M 0 0 L 10 5 L 0 10 z", fill=color)
    for di, diagram in enumerate(diagrams):
        validate(diagram)
        panel = element(root, "g", transform=f"translate({di * 420},0)",
                        data_diagram=diagram["name"])
        element(panel, "rect", x=12, y=82, width=396, height=502, rx=12,
                fill="white", stroke="#d0d9df")
        element(panel, "text", diagram["name"], x=30, y=114, font_size=21,
                font_weight="bold", fill="#192c3b")
        vertices = diagram["vertices"]
        count = len(vertices)
        positions = {}
        for i, vertex in enumerate(vertices):
            angle = -math.pi / 2 - 2 * math.pi * i / max(1, count)
            positions[vertex["id"]] = ((210, 270) if count == 1 else
                (210 + 90 * math.cos(angle), 290 + 90 * math.sin(angle)))
        groups = {}
        for edge in diagram["edges"]:
            key = tuple(sorted((edge["source"], edge["target"])))
            groups.setdefault(key, []).append(edge)
        for key, edges in groups.items():
            for index, edge in enumerate(edges):
                source, target = positions[edge["source"]], positions[edge["target"]]
                color_index = edge["generator"] % len(COLORS)
                color = COLORS[color_index]
                group = element(panel, "g", **{"class": "edge"},
                                data_edge_id=edge["id"], data_source=edge["source"],
                                data_target=edge["target"], data_generator=edge["generator"])
                element(group, "title", f"{edge['id']}: {edge['source']} → {edge['target']}; "
                        f"g{edge['generator']} = {json.dumps(edge['label'], ensure_ascii=False)}")
                if source == target:
                    angle = (-math.pi / 2 + index * 2 * math.pi / len(edges)
                             if count == 1 else math.atan2(source[1] - 290, source[0] - 210))
                    angle += (index - (len(edges) - 1) / 2) * 0.8 if count != 1 else 0
                    start = offset(source, (math.cos(angle - 0.6), math.sin(angle - 0.6)))
                    end = offset(source, (math.cos(angle + 0.6), math.sin(angle + 0.6)))
                    c1 = offset(source, (math.cos(angle - 0.7), math.sin(angle - 0.7)), 78)
                    c2 = offset(source, (math.cos(angle + 0.7), math.sin(angle + 0.7)), 78)
                    path = f"M {point(*start)} C {point(*c1)} {point(*c2)} {point(*end)}"
                    label = offset(source, (math.cos(angle), math.sin(angle)), 68)
                else:
                    low, high = positions[key[0]], positions[key[1]]
                    dx, dy = high[0] - low[0], high[1] - low[1]
                    length = math.hypot(dx, dy)
                    bend = (index - (len(edges) - 1) / 2) * 55
                    control = ((source[0] + target[0]) / 2 - dy / length * bend,
                               (source[1] + target[1]) / 2 + dx / length * bend)
                    start = offset(source, (control[0] - source[0], control[1] - source[1]))
                    end = offset(target, (control[0] - target[0], control[1] - target[1]))
                    path = f"M {point(*start)} Q {point(*control)} {point(*end)}"
                    label = ((start[0] + 2 * control[0] + end[0]) / 4,
                             (start[1] + 2 * control[1] + end[1]) / 4)
                element(group, "path", d=path, fill="none", stroke=color,
                        stroke_width=2.2, marker_end=f"url(#arrow{color_index})")
                element(group, "text", f"g{edge['generator']}", x=f"{label[0]:.2f}",
                        y=f"{label[1]:.2f}", text_anchor="middle", dominant_baseline="middle",
                        fill=color, stroke="white", stroke_width=5, paint_order="stroke")
        for vertex in vertices:
            x, y = positions[vertex["id"]]
            element(panel, "circle", cx=f"{x:.2f}", cy=f"{y:.2f}", r=18,
                    fill="#f1f5f8", stroke="#364b5b", stroke_width=1.5)
            element(panel, "text", vertex["label"], x=f"{x:.2f}", y=f"{y:.2f}",
                    text_anchor="middle", dominant_baseline="middle", fill="#192c3b")
        element(panel, "text", "Generator index = group label", x=30, y=441, fill="#435463")
        for i, generator in enumerate(diagram["generators"]):
            label = json.dumps(generator["label"], ensure_ascii=False, separators=(",", ":"))
            element(panel, "text", f"g{generator['id']} = {label}", x=30, y=468 + i * 25,
                    fill=COLORS[generator["id"] % len(COLORS)])
        element(panel, "text", f"{count} {'vertex' if count == 1 else 'vertices'} · {len(diagram['edges'])} directed edges",
                x=30, y=562, fill="#435463")
    ET.indent(root)
    return ET.tostring(root, encoding="unicode", xml_declaration=True) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.write_text(render(json.loads(args.input.read_text())), encoding="utf-8")


if __name__ == "__main__":
    main()
