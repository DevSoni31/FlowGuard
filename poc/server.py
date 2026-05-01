"""
server.py — Flask backend. Serves the dashboard and /api/result.
"""
import json
from pathlib import Path
from flask import Flask, jsonify, render_template

app = Flask(__name__)

@app.route("/")
def index():
    return render_template("index.html")

@app.route("/api/result")
def get_result():
    p = Path("result.json")
    if p.exists():
        return jsonify(json.loads(p.read_text()))
    return jsonify({"error": "No result yet"}), 404

def run():
    app.run(port=5050, debug=False, use_reloader=False)