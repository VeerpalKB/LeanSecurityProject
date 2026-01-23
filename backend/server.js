const express = require("express");
const path = require("path");

const app = express();
const PORT = 3000;

// Serve frontend
app.use(express.static(path.join(__dirname, "../frontend")));

app.get("/verify", (req, res) => {
  const property = req.query.property;

  let output;
  switch (property) {
    case "access_control":
      output = "Access control policy formally verified in Lean.";
      break;
    case "authentication":
      output = "Authentication verification not yet implemented.";
      break;
    case "encryption":
      output = "Encryption integrity verification planned for future work.";
      break;
    default:
      output = "Unknown property.";
  }

  res.json({ output });
});

// THIS PART IS CRITICAL
app.listen(PORT, () => {
  console.log(`Backend running at http://localhost:${PORT}`);
});