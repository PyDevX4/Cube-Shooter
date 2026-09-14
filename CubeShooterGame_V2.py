import pygame
import os
import sys
import math
import random
import time
import atexit
import base64
import json
import zlib

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # So the game finds cube_accounts.py next to it
import cube_accounts
import cube_online
import cube_net
import updater
import sounds  # Sound effects: files dropped in the "sounds" folder play on their events
from version import VERSION

# Auto-update (built .exe only): looks for a newer release in the background and installs it from a menu
auto_updater = updater.AutoUpdater()
auto_updater.start()

global equipped_ability

print("=== GAME STARTED ===")

pygame.init()

# Match the shape of this screen, so fullscreen fills it with no black bars and nothing is stretched.
# The height stays 900, and the width follows the monitor (1440 on a 16:10 screen, 1600 on 16:9).
HEIGHT = 900
try:
    desktop_width, desktop_height = pygame.display.get_desktop_sizes()[0]
    screen_aspect = min(2.1, max(1.3, desktop_width / desktop_height))  # Sane limits for odd monitors
except (pygame.error, IndexError, ZeroDivisionError):
    screen_aspect = 16 / 9
WIDTH = int(round(HEIGHT * screen_aspect / 2)) * 2  # Even number keeps halves tidy
# SCALED keeps that layout but lets the window be resized or maximized (the square
# button in the title bar). pygame scales the picture to fit and translates mouse positions for us.
os.environ.setdefault("SDL_RENDER_SCALE_QUALITY", "1")  # Smooth scaling instead of blocky pixels
try:
    screen = pygame.display.set_mode((WIDTH, HEIGHT), pygame.SCALED | pygame.RESIZABLE)
except pygame.error:
    screen = pygame.display.set_mode((WIDTH, HEIGHT))  # Fallback for systems that can't scale
pygame.display.set_caption("Cube Shooter")
clock = pygame.time.Clock()

font = pygame.font.SysFont(None, 72)
button_font = pygame.font.SysFont(None, 48)
smaller_button_font = pygame.font.SysFont(None, 30)
small_button_font = pygame.font.SysFont(None, 30)
coin_font = pygame.font.SysFont(None, 36)

BLACK = (0, 0, 0)
BLUE = (0, 0, 255)
RED = (255, 0, 0)
WHITE = (255, 255, 255)
YELLOW = (255, 255, 0)
GREEN = (0, 255, 0)
ORANGE = (255, 165, 0)
PURPLE = (128, 0, 128)
DARK_RED = (200, 0, 0)

player_size = 50
mini_size = 20
bullet_size = 8
coin_radius = 6
safe_spawn_distance = 150
wave_completion_reward = 15  # Coins shown on the wave complete banner (100 for a boss wave)

invincible = False  # Track invincibility state

# Game state variables
start_screen = True
game_mode_selection = False
game_over = False
game_paused = False
pause_countdown = 0
pause_countdown_duration = 3.0
coin_cheat_enabled = False
kill_cheat_enabled = False
no_death_cheat_enabled = False

# Code console (press ` at any time to type a cheat code)
CHEAT_CODES = {
    "coinhack": "coin",   # L gives +1000 coins
    "killhack": "kill",   # K kills every enemy
    "god": "no_death",    # M toggles invincibility
}
console_open = False
console_input = ""
console_was_paused = False
console_message = ""
console_message_timer = 0.0
in_block_defence = False

coins = []
coin_count = 0

# Separate coin systems for each game mode
main_game_coins = 0  # Store coins from main game mode
block_defence_coins = 0  # Store coins from block defence mode
main_game_skin = "white"  # Store skin from main game mode
main_game_owned_skins = {
    "white": True,
    "black": True,
    "red": False,
    "orange": False,
    "yellow": False,
    "green": False,
    "blue": False,
    "purple": False,
    "rainbow": False,
    "galaxy": False,
    "lava": False,
    "water": False
}  # Store owned skins from main game mode
# Store upgrade states from main game mode
main_game_has_gun_upgrade = False
main_game_has_gun_upgrade_1 = False
main_game_has_gun_upgrade_2 = False
main_game_has_gun_upgrade_3 = False
main_game_has_gun_upgrade_4 = False
main_game_has_gun_upgrade_5 = False
main_game_has_magnet_1 = False
main_game_has_magnet_2 = False
main_game_has_magnet_3 = False
main_game_has_magnet_4 = False
main_game_has_magnet_5 = False
main_game_has_shield = False
main_game_has_teleport = False
main_game_has_freeze = False
main_game_has_shockwave = False
main_game_has_helpers = False
main_game_has_coin_controller = False
main_game_has_triple_bullet = False
main_game_equipped_ability = None  # Store equipped ability from main game mode
main_game_shot_delay = 0.5  # Store shot delay from main game mode

# Start player color default white
player_color = WHITE
mini_color = WHITE

owned_skins = {
    "white": True,
    "black": True,
    "red": False,
    "orange": False,
    "yellow": False,
    "green": False,
    "blue": False,
    "purple": False,
    "rainbow": False,  # new rainbow skin
    "galaxy": False,  # new galaxy skin
    "lava": False,  # new lava skin
    "water": False  # new water skin
}

skin_colors = {
    "white": WHITE,
    "black": BLACK,
    "red": RED,
    "orange": ORANGE,
    "yellow": YELLOW,
    "green": GREEN,
    "blue": BLUE,
    "purple": PURPLE,
    "lava": (255, 69, 0),  # Lava orange-red color
    "water": (0, 150, 255),  # Water blue color
    # rainbow handled separately
    # galaxy handled separately
}

# List of skins in shop order
shop_skins = ["white", "black", "red", "galaxy", "orange", "yellow", "green", "blue", "purple", "lava", "water", "rainbow"]

current_skin = "white"

red_enemies = []
green_enemies = []
red_enemy_speed = 1.5
green_enemy_speed = 3.0
player_speed = 5
max_red_enemies = 1
max_green_enemies = 0
kills = 0
wave = 1

# Map size (takes 5 seconds to walk to edge from spawn)
distance_to_edge = player_speed * 5 * 60  # 5 seconds at 60 FPS
MAP_WIDTH = int(distance_to_edge * 2 + player_size)
MAP_HEIGHT = int(distance_to_edge * 2 + player_size)

# Storm survival shrinking map variables
storm_survival_map_width = MAP_WIDTH
storm_survival_map_height = MAP_HEIGHT

last_shot_time = 0
shot_delay = 0.5

blue_enemies = []
max_blue_enemies = 0
blue_enemy_speed = red_enemy_speed
blue_bullets = []  # List of dicts: {x, y, dx, dy}, plus "scale" for bigger shots (x, y is the top-left of the shot's box)
BLUE_BOSS_SHOT_SCALE = 3  # The Blue Boss's lasers are 3 times bigger than normal

def shot_size(shot):
    return bullet_size * shot.get("scale", 1)
blue_bullet_speed = 7
BLUE_SHOOT_RANGE = 840  # Blue enemies only shoot when this close (about twice the orange's laser range)
blue_last_shot_times = []  # One per blue enemy
blue_shot_delay = 1.5

# Purple enemy variables
purple_enemies = []
max_purple_enemies = 0
purple_enemy_speed = 0.5  # Very slow speed
purple_mini_circles = []  # List of lists: each purple enemy has up to 4 mini circles, each [x, y, angle]
purple_mini_size = 16  # Size of mini circles
purple_mini_tether = 60  # Distance from the big purple's center to each mini circle
purple_mini_spin_speed = 0.02  # How fast the mini circles rotate around the big purple (radians per frame)

# Gun upgrade state
has_gun_upgrade = False
has_gun_upgrade_1 = False
has_gun_upgrade_2 = False
has_gun_upgrade_3 = False
has_gun_upgrade_4 = False
has_gun_upgrade_5 = False
has_magnet_1 = False
has_magnet_2 = False
has_magnet_3 = False
has_magnet_4 = False
has_magnet_5 = False
has_shield = False
has_teleport = False
has_freeze = False
equipped_ability = None  # 'shield', 'teleport', or 'freeze'

# Track if shield is active
shield_active = False
shield_cooldown = 0.0
shield_timer = 0.0
shield_cooldown_time = 5.0
shield_max_duration = 3.0

# Track teleport cooldown
teleport_cooldown = 0.0
teleport_cooldown_time = 10.0

# Track freeze ability
freeze_active = False
freeze_cooldown = 0.0
freeze_cooldown_time = 10.0
freeze_duration = 5.0
freeze_timer = 0.0

# Track shockwave ability
has_shockwave = False
shockwave_active = False
shockwave_cooldown = 0.0
shockwave_cooldown_time = 15.0
shockwave_duration = 1.0
shockwave_timer = 0.0
shockwave_radius = 0
shockwave_max_radius = 300

# Track helpers ability
has_helpers = False
helpers_active = False
helpers_cooldown = 0.0
helpers_cooldown_time = 30.0
helpers_duration = 10.0
helpers_timer = 0.0
helpers = []  # List of helper dicts: {x, y, angle, last_shot_time, skin}
helper_speed = 3.0
helper_size = 20

# Wave completion system
wave_completion_message = ""
wave_completion_timer = 0.0
wave_completion_duration = 3.0  # How long to show the message
last_wave = 1

# Game timer
game_timer = 0.0

# Camera offset for unlimited map
camera_x = 0
camera_y = 0

# Pause system
pause_countdown = 0.0
pause_countdown_duration = 3.0

# Track Coin Controller ability
has_coin_controller = False
coin_controller_cooldown = 0.0
coin_controller_cooldown_time = 10.0
coin_controller_active = False
coin_controller_duration = 3.0
coin_controller_timer = 0.0
coin_attraction_speed = 800.0


# Track Triple Bullet ability
has_triple_bullet = False
triple_bullet_active = False
triple_bullet_cooldown = 0.0
triple_bullet_cooldown_time = 20.0
triple_bullet_duration = 10.0
triple_bullet_timer = 0.0

# Shooting range editor mode
shooting_range_editor_mode = True
shooting_range_play_mode = False

# Orbit variables for mini gun
orbit_x = 0
orbit_y = 0

# Add at the top, after player_size and before game state variables
BLOCK_DEFENCE_BLOCK_W = 133  # 1.5 times smaller than the old 200
BLOCK_DEFENCE_BLOCK_H = 133
BLOCK_DEFENCE_BLOCK_COLOR = (120, 120, 120)
# The block is centered horizontally, and 100px below the player spawn
BLOCK_DEFENCE_BLOCK_RECT = pygame.Rect(
    MAP_WIDTH // 2 - BLOCK_DEFENCE_BLOCK_W // 2,
    MAP_HEIGHT // 2 + player_size // 2 + 350,  # 350px gap below player (moved down from 50px)
    BLOCK_DEFENCE_BLOCK_W,
    BLOCK_DEFENCE_BLOCK_H
)
# Block health for Block Defence mode
block_health = 50
BLOCK_MAX_HEALTH = 50
block_defence_points = 0   # Earned per kill in Block Defence; spent on repairing the block
block_hit_flash = 0.0      # Seconds of white flash left after the block takes a hit
block_menu_open = False
block_menu_anim = 0.0
block_menu_was_paused = False
BLOCK_REPAIRS = [(5, 3), (15, 8), (BLOCK_MAX_HEALTH, 15)]  # (health, points); the last one is a full repair
# Block Defence game over timer
block_defence_game_over_timer = 0.0

def _glow_dot(surface, center, radius, color, alpha=255):
    """Additive blob of light, brightest in the middle - the building block for all the glows below."""
    radius = max(1, int(radius))
    dot = pygame.Surface((radius * 2, radius * 2), pygame.SRCALPHA)
    for r in range(radius, 0, -1):
        pygame.draw.circle(dot, (*color, int(alpha * (1 - r / radius) ** 1.8)), (radius, radius), r)
    surface.blit(dot, (center[0] - radius, center[1] - radius), special_flags=pygame.BLEND_RGBA_ADD)

def create_galaxy_surface(size=150):
    """Deep space: two glowing spiral arms winding around a bright core, over nebula clouds and stars."""
    rng = random.Random(11)  # Fixed seed so the skin looks the same every run
    surf = pygame.Surface((size, size))
    surf.fill((8, 6, 24))
    center = (size / 2, size / 2)
    _glow_dot(surf, center, size * 0.55, (35, 25, 90), 170)
    # Nebula clouds
    for _ in range(18):
        angle = rng.uniform(0, 2 * math.pi)
        distance = rng.uniform(0, size * 0.45)
        cloud = (center[0] + math.cos(angle) * distance, center[1] + math.sin(angle) * distance)
        _glow_dot(surf, cloud, rng.uniform(size * 0.10, size * 0.25), rng.choice([(70, 30, 120), (25, 45, 120), (90, 35, 90)]), 110)
    # Two spiral arms of star dust, pink near the core fading to blue at the rim
    for arm in range(2):
        for step in range(150):
            t = step / 149
            angle = t * 3.3 + arm * math.pi + rng.uniform(-0.05, 0.05)
            distance = t * size * 0.47 + rng.uniform(-size * 0.02, size * 0.02)
            point = (center[0] + math.cos(angle) * distance, center[1] + math.sin(angle) * distance)
            _glow_dot(surf, point, size * (0.05 - 0.03 * t) + 1, (int(255 - 120 * t), int(190 - 60 * t), 255), 90)
    # Bright core
    _glow_dot(surf, center, size * 0.20, (120, 90, 200), 200)
    _glow_dot(surf, center, size * 0.10, (255, 230, 255), 255)
    # Star field, plus a few big stars with cross flares
    for _ in range(90):
        shade = rng.randint(170, 255)
        pygame.draw.circle(surf, (shade, shade, min(255, shade + 20)), (rng.randrange(size), rng.randrange(size)), 1)
    for _ in range(7):
        x, y = rng.randrange(6, size - 6), rng.randrange(6, size - 6)
        _glow_dot(surf, (x, y), 5, (200, 220, 255), 220)
        pygame.draw.line(surf, WHITE, (x - 4, y), (x + 4, y))
        pygame.draw.line(surf, WHITE, (x, y - 4), (x, y + 4))
    return surf

galaxy_texture = create_galaxy_surface()

def create_lava_surface(size=150):
    """Dark volcanic crust cracked open by white-hot molten veins, with glowing pools and embers."""
    rng = random.Random(5)
    surf = pygame.Surface((size, size))
    surf.fill((26, 12, 10))
    # Mottled, rocky crust
    for _ in range(220):
        shade = rng.choice([(44, 24, 20), (16, 8, 8), (54, 30, 24)])
        pygame.draw.circle(surf, shade, (rng.randrange(size), rng.randrange(size)), rng.randint(3, 10))
    # Molten pools glowing up through the rock, built from overlapping blobs so they look uneven
    for _ in range(4):
        pool_x, pool_y = rng.randrange(size), rng.randrange(size)
        radius = rng.uniform(size * 0.10, size * 0.18)
        for _ in range(3):
            blob = (pool_x + rng.uniform(-radius, radius) * 0.6, pool_y + rng.uniform(-radius, radius) * 0.6)
            _glow_dot(surf, blob, radius, (190, 55, 0), 170)
        _glow_dot(surf, (pool_x, pool_y), radius * 0.5, (255, 180, 40), 210)
    # Cracks: wandering paths, charred at the edges and white-hot in the middle
    for _ in range(5):
        x, y = rng.randrange(size), rng.randrange(size)
        angle = rng.uniform(0, 2 * math.pi)
        path = [(x, y)]
        for _ in range(rng.randint(18, 30)):
            angle += rng.uniform(-0.55, 0.55)
            x += math.cos(angle) * 6
            y += math.sin(angle) * 6
            path.append((x, y))
        pygame.draw.lines(surf, (70, 20, 8), False, path, 7)
        glow_layer = pygame.Surface((size, size), pygame.SRCALPHA)
        pygame.draw.lines(glow_layer, (255, 90, 0, 60), False, path, 9)
        pygame.draw.lines(glow_layer, (255, 130, 20, 110), False, path, 5)
        surf.blit(glow_layer, (0, 0), special_flags=pygame.BLEND_RGBA_ADD)
        pygame.draw.lines(surf, (255, 150, 30), False, path, 2)
        pygame.draw.lines(surf, (255, 240, 170), False, path, 1)
    # Embers
    for _ in range(45):
        color = rng.choice([(255, 170, 40), (255, 225, 150), (255, 110, 20)])
        _glow_dot(surf, (rng.randrange(size), rng.randrange(size)), rng.uniform(2, 4), color, 200)
    return surf

lava_texture = create_lava_surface()

def create_water_surface(size=150):
    """Deep water seen from above: sunlight caustics rippling over rolling waves, with foam sparkles."""
    rng = random.Random(3)
    surf = pygame.Surface((size, size))
    # Sunlit near the top, deep blue further down
    for y in range(size):
        t = y / (size - 1)
        surf.fill((int(20 - 14 * t), int(90 - 55 * t), int(160 - 70 * t)), (0, y, size, 1))
    # Deeper patches
    for _ in range(10):
        pygame.draw.circle(surf, (0, 40, 95), (rng.randrange(size), rng.randrange(size)), rng.randint(10, 26))
    # Caustics: broken, squashed arcs of light, like sun shining through a rippling surface
    for _ in range(46):
        cx, cy = rng.randrange(size), rng.randrange(size)
        radius = rng.randint(10, 30)
        squash = rng.uniform(0.45, 0.9)  # Flattened, so they look like ripples seen at an angle
        arc_surf = pygame.Surface((radius * 2 + 6, radius * 2 + 6), pygame.SRCALPHA)
        box = pygame.Rect(3, 3 + radius * (1 - squash), radius * 2, radius * 2 * squash)
        start = rng.uniform(0, 2 * math.pi)
        pygame.draw.arc(arc_surf, (130, 225, 255, rng.randint(45, 95)), box, start, start + rng.uniform(1.2, 4.0), 2)
        surf.blit(arc_surf, (cx - radius - 3, cy - radius - 3), special_flags=pygame.BLEND_RGBA_ADD)
    # Wave crests rolling across
    for band in range(7):
        y0 = band * size / 7 + rng.uniform(-4, 4)
        points = [(x, y0 + math.sin(x / 9 + band) * 4) for x in range(0, size + 6, 6)]
        pygame.draw.lines(surf, (90, 190, 240), False, points, 2)
        pygame.draw.lines(surf, (190, 245, 255), False, [(x, y - 2) for x, y in points], 1)
    # Foam sparkles
    for _ in range(40):
        _glow_dot(surf, (rng.randrange(size), rng.randrange(size)), rng.uniform(2, 4), (200, 245, 255), 200)
    return surf

water_texture = create_water_surface()

def create_grass_surface(tile_size=128):
    """Seamless grass tile: soft light/dark patches covered in small grass blades."""
    rng = random.Random(7)  # Fixed seed so the grass looks the same every run
    surf = pygame.Surface((tile_size, tile_size))
    surf.fill((52, 140, 48))
    offsets = (-tile_size, 0, tile_size)  # Also draw across the edges so the tile wraps seamlessly
    for _ in range(18):
        x, y = rng.randrange(tile_size), rng.randrange(tile_size)
        radius = rng.randint(10, 26)
        color = rng.choice([(58, 148, 52), (47, 132, 44), (62, 154, 56)])
        for ox in offsets:
            for oy in offsets:
                pygame.draw.circle(surf, color, (x + ox, y + oy), radius)
    blade_colors = [(36, 112, 36), (44, 124, 40), (70, 164, 60), (84, 178, 70)]
    for _ in range(520):
        x, y = rng.randrange(tile_size), rng.randrange(tile_size)
        length = rng.randint(4, 9)
        lean = rng.randint(-3, 3)
        color = rng.choice(blade_colors)
        for ox in offsets:
            for oy in offsets:
                pygame.draw.line(surf, color, (x + ox, y + oy), (x + ox + lean, y + oy - length))
    return surf

grass_texture = create_grass_surface()

def create_snow_surface(tile_size=128):
    """Seamless snow tile: soft drifts in white and pale blue, with glittering specks."""
    rng = random.Random(9)
    surf = pygame.Surface((tile_size, tile_size))
    surf.fill((226, 234, 243))
    offsets = (-tile_size, 0, tile_size)  # Draw across the edges so the tile wraps seamlessly
    for _ in range(22):
        x, y = rng.randrange(tile_size), rng.randrange(tile_size)
        radius = rng.randint(10, 28)
        color = rng.choice([(236, 242, 249), (214, 225, 238), (244, 248, 252), (206, 219, 234)])
        for ox in offsets:
            for oy in offsets:
                pygame.draw.circle(surf, color, (x + ox, y + oy), radius)
    for _ in range(170):
        x, y = rng.randrange(tile_size), rng.randrange(tile_size)
        color = rng.choice([(255, 255, 255), (255, 255, 255), (190, 208, 228), (170, 196, 225)])
        size = rng.choice((1, 1, 2))
        for ox in offsets:
            for oy in offsets:
                pygame.draw.circle(surf, color, (x + ox, y + oy), size)
    return surf

def create_sand_surface(tile_size=128):
    """Seamless sand tile: warm dune patches, wind ripples and scattered grains."""
    rng = random.Random(13)
    surf = pygame.Surface((tile_size, tile_size))
    surf.fill((222, 194, 138))
    offsets = (-tile_size, 0, tile_size)
    for _ in range(18):
        x, y = rng.randrange(tile_size), rng.randrange(tile_size)
        radius = rng.randint(10, 26)
        color = rng.choice([(230, 204, 148), (212, 182, 126), (236, 212, 158)])
        for ox in offsets:
            for oy in offsets:
                pygame.draw.circle(surf, color, (x + ox, y + oy), radius)
    for band in range(6):  # Ripples: two full waves across the tile, so the left and right edges line up
        y0 = band * tile_size / 6 + rng.uniform(0, 8)
        points = [(x, y0 + math.sin(x / tile_size * 4 * math.pi + band) * 3) for x in range(0, tile_size + 1, 4)]
        for oy in offsets:
            pygame.draw.lines(surf, (200, 168, 112), False, [(px, py + oy) for px, py in points], 1)
            pygame.draw.lines(surf, (240, 220, 170), False, [(px, py + oy - 1) for px, py in points], 1)
    for _ in range(260):
        surf.set_at((rng.randrange(tile_size), rng.randrange(tile_size)),
                    rng.choice([(190, 158, 104), (178, 144, 92), (246, 226, 180)]))
    return surf

MAP_NAMES = ["Grass", "Snow", "Sand"]
MAP_TEXTURES = {"Grass": grass_texture, "Snow": create_snow_surface(), "Sand": create_sand_surface()}
MINIMAP_GROUND = {"Grass": (46, 96, 46, 230), "Snow": (170, 188, 205, 230), "Sand": (175, 145, 92, 230)}
selected_map = "Grass"

def create_metal_surface(width, height):
    """Dark brushed-steel background with bolted panels, used behind menus."""
    rng = random.Random(3)
    surf = pygame.Surface((width, height))
    for y in range(height):
        t = y / height
        surf.fill((int(86 - 40 * t), int(92 - 42 * t), int(100 - 43 * t)), (0, y, width, 1))
    # Brushed streaks
    streaks = pygame.Surface((width, height), pygame.SRCALPHA)
    for _ in range(1800):
        y = rng.randrange(height)
        x = rng.randrange(-100, width)
        length = rng.randint(40, 300)
        if rng.random() < 0.5:
            color = (255, 255, 255, rng.randint(6, 22))
        else:
            color = (0, 0, 0, rng.randint(10, 30))
        pygame.draw.line(streaks, color, (x, y), (x + length, y))
    surf.blit(streaks, (0, 0))
    # Panel seams with a small bevel, and a rivet near each panel corner
    panel_w, panel_h = width // 4, height // 3
    for px in range(0, width + 1, panel_w):
        pygame.draw.line(surf, (28, 30, 34), (px, 0), (px, height), 3)
        pygame.draw.line(surf, (120, 126, 134), (px + 2, 0), (px + 2, height), 1)
    for py in range(0, height + 1, panel_h):
        pygame.draw.line(surf, (28, 30, 34), (0, py), (width, py), 3)
        pygame.draw.line(surf, (120, 126, 134), (0, py + 2), (width, py + 2), 1)
    for px in range(0, width, panel_w):
        for py in range(0, height, panel_h):
            for rx, ry in ((14, 14), (panel_w - 14, 14), (14, panel_h - 14), (panel_w - 14, panel_h - 14)):
                cx, cy = px + rx, py + ry
                pygame.draw.circle(surf, (30, 32, 36), (cx + 1, cy + 2), 5)
                pygame.draw.circle(surf, (140, 146, 154), (cx, cy), 5)
                pygame.draw.circle(surf, (190, 196, 204), (cx - 1, cy - 1), 2)
    return surf

metal_background = create_metal_surface(WIDTH, HEIGHT)

def create_bubble_text(text, size, top_color, bottom_color, outline_color=(20, 24, 48), outline=9):
    """Render chunky 'bubble' letters: gradient fill, glossy highlight, thick round outline and a drop shadow."""
    # Cooper Black is a round, bubbly font that ships with Windows; fall back to a bold default font
    if "cooperblack" in pygame.font.get_fonts():
        bubble_font = pygame.font.SysFont("cooperblack", size)
    else:
        bubble_font = pygame.font.SysFont(None, size, bold=True)
    mask = bubble_font.render(text, True, WHITE)
    w, h = mask.get_size()
    pad = outline + 10
    size_with_pad = (w + pad * 2, h + pad * 2)
    # Thick rounded outline: stamp the text all around a circle
    outline_mask = bubble_font.render(text, True, outline_color)
    stamps = {(round(math.cos(k * math.pi / 12) * r), round(math.sin(k * math.pi / 12) * r))
              for r in range(1, outline + 1) for k in range(24)}
    outline_layer = pygame.Surface(size_with_pad, pygame.SRCALPHA)
    for dx, dy in stamps:
        outline_layer.blit(outline_mask, (pad + dx, pad + dy))
    shadow_layer = outline_layer.copy()
    shadow_layer.fill((0, 0, 0, 120), special_flags=pygame.BLEND_RGBA_MULT)
    surf = pygame.Surface(size_with_pad, pygame.SRCALPHA)
    surf.blit(shadow_layer, (6, 8))
    surf.blit(outline_layer, (0, 0))
    # Top-to-bottom gradient, cut to the letter shapes
    fill = pygame.Surface((w, h), pygame.SRCALPHA)
    for y in range(h):
        t = y / max(1, h - 1)
        fill.fill(tuple(int(top_color[i] + (bottom_color[i] - top_color[i]) * t) for i in range(3)), (0, y, w, 1))
    fill.blit(mask, (0, 0), special_flags=pygame.BLEND_RGBA_MULT)
    surf.blit(fill, (pad, pad))
    # Glossy shine across the top half of the letters
    gloss = mask.copy()
    gloss.fill((255, 255, 255, 90), special_flags=pygame.BLEND_RGBA_MULT)
    gloss.fill((0, 0, 0, 0), (0, int(h * 0.48), w, h))
    surf.blit(gloss, (pad, pad))
    return surf

title_cube_surface = create_bubble_text("Cube", 150, (130, 230, 255), (20, 110, 230))
title_shooter_surface = create_bubble_text("Shooter", 130, (255, 225, 90), (240, 90, 30))

GREY_BUTTON = (95, 100, 110)  # Can't be used right now

def draw_button(rect, color=BLUE):
    """Draw a white button with a dark outline. GREEN / DARK_RED / YELLOW tint it for owned, can't-afford and toggle states."""
    fill = {GREEN: (170, 235, 170), DARK_RED: (240, 165, 165), YELLOW: (250, 238, 150), GREY_BUTTON: (150, 154, 162)}.get(color, WHITE)
    pygame.draw.rect(screen, (15, 15, 15), rect.move(0, 4), border_radius=8)
    pygame.draw.rect(screen, fill, rect, border_radius=8)
    pygame.draw.rect(screen, (35, 35, 35), rect, 2, border_radius=8)

def create_orb_sprite(base_color, radius, glow=10):
    """Pre-render a shaded, 3D-looking orb: dark rim, lit top-left side, specular shine and a soft outer glow."""
    def mix(a, b, t):
        return tuple(int(a[i] + (b[i] - a[i]) * t) for i in range(3))
    size = (radius + glow) * 2
    c = size // 2
    surf = pygame.Surface((size, size), pygame.SRCALPHA)
    # Soft outer glow, fading out from the edge of the orb
    for i in range(glow, 0, -1):
        pygame.draw.circle(surf, (*base_color, int(70 * (1 - i / glow) ** 2)), (c, c), radius + i)
    # Sphere shading: rings shrink toward a lit spot at the top-left, going dark rim -> base color -> light
    dark = tuple(int(v * 0.3) for v in base_color)
    light = mix(base_color, (255, 255, 255), 0.5)
    for r in range(radius, 0, -1):
        t = 1 - r / radius
        color = mix(dark, base_color, t * 2) if t < 0.5 else mix(base_color, light, (t - 0.5) * 2)
        pygame.draw.circle(surf, color, (c - radius * 0.35 * t, c - radius * 0.4 * t), r)
    # Specular shine and a faint rim light (drawn on a separate layer so they blend instead of cutting holes)
    shine = pygame.Surface((size, size), pygame.SRCALPHA)
    pygame.draw.ellipse(shine, (255, 255, 255, 110), (c - radius * 0.62, c - radius * 0.72, radius * 0.7, radius * 0.45))
    pygame.draw.ellipse(shine, (255, 255, 255, 200), (c - radius * 0.5, c - radius * 0.62, radius * 0.35, radius * 0.22))
    pygame.draw.circle(shine, (*light, 60), (c, c), radius, 2)
    surf.blit(shine, (0, 0))
    return surf

def create_shadow_sprite(radius):
    """Soft oval ground shadow for an orb of the given radius."""
    w, h = radius * 2 + 6, radius + 6
    surf = pygame.Surface((w, h), pygame.SRCALPHA)
    for i, alpha in enumerate((30, 55, 80)):
        inset = i * 3
        pygame.draw.ellipse(surf, (0, 0, 0, alpha), (inset, inset // 2, w - inset * 2, h - inset))
    return surf

def draw_shadow(shadow, cx, cy):
    screen.blit(shadow, (cx - shadow.get_width() // 2 + 5, cy - shadow.get_height() // 2 + shadow.get_height() * 0.7))

def draw_orb(orb, shadow, cx, cy):
    """Draw a pre-rendered orb centered on (cx, cy), with its ground shadow if given."""
    if shadow is not None:
        draw_shadow(shadow, cx, cy)
    screen.blit(orb, (cx - orb.get_width() // 2, cy - orb.get_height() // 2))

# Skins that use a texture instead of a flat color, and the glow color for skins that need a custom one
SKIN_TEXTURES = {"galaxy": galaxy_texture, "lava": lava_texture, "water": water_texture}
SKIN_GLOWS = {"galaxy": (100, 150, 255), "lava": (255, 69, 0), "water": (0, 150, 255), "black": (110, 110, 130)}

def draw_player_cube(x, y, face, glow_color, aim_angle, size=None):
    """Draw the player as a beveled 3D cube: ground shadow, soft glow, shaded face (color or texture),
    light/dark bevel edges and a visor that slides toward where you're aiming."""
    s = size or player_size
    k = s / player_size  # Scale factor for bigger previews (like the skin shop cards)
    # Ground shadow
    shadow = pygame.Surface((s + round(8 * k), s + round(8 * k)), pygame.SRCALPHA)
    pygame.draw.rect(shadow, (0, 0, 0, 70), shadow.get_rect(), border_radius=round(8 * k))
    screen.blit(shadow, (x + 5 * k, y + 7 * k))
    # Soft glow in the skin color, stronger toward the cube
    pad = round(12 * k)
    glow = pygame.Surface((s + pad * 2, s + pad * 2), pygame.SRCALPHA)
    for i, alpha in enumerate((25, 45, 70)):
        pygame.draw.rect(glow, (*glow_color[:3], alpha), glow.get_rect().inflate(-i * pad * 2 // 3, -i * pad * 2 // 3), border_radius=round((12 - i * 3) * k))
    screen.blit(glow, (x - pad, y - pad))
    # Face: skin texture or flat color
    body = pygame.Surface((s, s), pygame.SRCALPHA)
    if isinstance(face, pygame.Surface):
        body.blit(pygame.transform.smoothscale(face, (s, s)), (0, 0))
    else:
        body.fill(face[:3])
    # Lighting (brighter top, darker bottom) and bevel (light top/left edges, dark bottom/right edges).
    # Drawn on a separate layer so it blends over the face instead of replacing it.
    light = pygame.Surface((s, s), pygame.SRCALPHA)
    for row in range(s):
        t = row / (s - 1)
        if t < 0.5:
            light.fill((255, 255, 255, int(70 * (0.5 - t) * 2)), (0, row, s, 1))
        else:
            light.fill((0, 0, 0, int(90 * (t - 0.5) * 2)), (0, row, s, 1))
    b = max(3, round(5 * k))
    pygame.draw.polygon(light, (255, 255, 255, 110), [(0, 0), (s, 0), (s - b, b), (b, b), (b, s - b), (0, s)])
    pygame.draw.polygon(light, (0, 0, 0, 110), [(s, s), (0, s), (b, s - b), (s - b, s - b), (s - b, b), (s, 0)])
    body.blit(light, (0, 0))
    # Round the corners slightly
    corner_mask = pygame.Surface((s, s), pygame.SRCALPHA)
    pygame.draw.rect(corner_mask, (255, 255, 255, 255), corner_mask.get_rect(), border_radius=round(6 * k))
    body.blit(corner_mask, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
    screen.blit(body, (x, y))
    pygame.draw.rect(screen, (20, 20, 25), (x, y, s, s), max(2, round(2 * k)), border_radius=round(6 * k))
    # Visor: a dark slot pushed toward the aim direction, with a pulsing cyan core
    vx = x + s / 2 + math.cos(aim_angle) * 7 * k
    vy = y + s / 2 + math.sin(aim_angle) * 7 * k
    visor = pygame.Rect(0, 0, 26 * k, 12 * k)
    visor.center = (vx, vy)
    pygame.draw.rect(screen, (15, 18, 28), visor, border_radius=round(5 * k))
    pulse = (math.sin(pygame.time.get_ticks() / 200) + 1) / 2
    core = pygame.Rect(0, 0, 16 * k, 4 * k)
    core.center = (vx, vy)
    pygame.draw.rect(screen, (int(90 + 60 * pulse), int(200 + 40 * pulse), 255), core, border_radius=2)

# Plasma laser bolts (pre-rendered pointing right; rotated copies are cached in 5-degree steps)
LASER_LENGTH = 30

def create_laser_sprite(core_color, glow_color, length=LASER_LENGTH, thickness=6):
    """Pre-render a plasma bolt pointing right: a soft colored glow around a white-hot core."""
    pad = 7
    surf = pygame.Surface((length + pad * 2, thickness + pad * 2), pygame.SRCALPHA)
    mid = surf.get_height() // 2
    for spread, alpha in ((pad, 45), (pad * 2 // 3, 90), (pad // 3, 150)):
        h = thickness + spread * 2
        pygame.draw.rect(surf, (*glow_color, alpha), (pad - spread, mid - h // 2, length + spread * 2, h), border_radius=h // 2)
    pygame.draw.rect(surf, core_color, (pad, mid - thickness // 2, length, thickness), border_radius=thickness // 2)
    pygame.draw.rect(surf, WHITE, (pad + 4, mid - 1, length - 8, 2), border_radius=1)
    return surf

LASER_SPRITES = {
    "player": create_laser_sprite((120, 200, 255), (40, 120, 255)),  # Blue plasma
    "enemy": create_laser_sprite((255, 120, 110), (255, 30, 30)),    # Red plasma
}
laser_cache = {}

def draw_laser(kind, x, y, dx, dy, scale=1):
    """Draw a plasma bolt whose head is at screen position (x, y), trailing back along its velocity (dx, dy)."""
    angle = round(math.degrees(math.atan2(-dy, dx)) / 5) * 5 % 360
    sprite = laser_cache.get((kind, angle, scale))
    if sprite is None:
        base = LASER_SPRITES[kind]
        if scale != 1:
            base = pygame.transform.smoothscale(base, (base.get_width() * scale, base.get_height() * scale))
        sprite = pygame.transform.rotate(base, angle)
        laser_cache[(kind, angle, scale)] = sprite
    speed = math.hypot(dx, dy) or 1
    back = LASER_LENGTH * scale / 2
    screen.blit(sprite, sprite.get_rect(center=(x - dx / speed * back, y - dy / speed * back)))

def draw_muzzle_flash(x, y, color, age, duration=0.08):
    """Quick burst of light where a laser was just fired (age = seconds since the shot)."""
    if not 0 <= age <= duration:
        return
    t = age / duration
    radius = int(6 + 8 * t)
    surf = pygame.Surface((radius * 2 + 2, radius * 2 + 2), pygame.SRCALPHA)
    c = radius + 1
    pygame.draw.circle(surf, (*color, int(180 * (1 - t))), (c, c), radius)
    pygame.draw.circle(surf, (255, 255, 255, int(230 * (1 - t))), (c, c), max(1, radius // 2))
    screen.blit(surf, (x - c, y - c))

def draw_eye(cx, cy, look_x, look_y, radius, offset):
    """Robotic visor eye (same style as the player's) on an enemy centered at (cx, cy): a dark slot
    that slides `offset` px toward what it's looking at (look_x, look_y), with a pulsing red light strip."""
    dx, dy = look_x - cx, look_y - cy
    dist = math.hypot(dx, dy) or 1
    vx, vy = cx + dx / dist * offset, cy + dy / dist * offset
    visor = pygame.Rect(0, 0, radius * 3, max(4, radius * 1.4))
    visor.center = (vx, vy)
    pygame.draw.rect(screen, (15, 18, 28), visor, border_radius=max(2, int(radius * 0.6)))
    pulse = (math.sin(pygame.time.get_ticks() / 200) + 1) / 2
    core = pygame.Rect(0, 0, radius * 1.9, max(2, radius * 0.45))
    core.center = (vx, vy)
    pygame.draw.rect(screen, (255, int(60 + 60 * pulse), int(50 + 40 * pulse)), core, border_radius=max(1, int(radius * 0.25)))

# Death effects: an expanding flash ring plus spinning shards in the enemy's color
EFFECT_COLORS = {"red": (225, 35, 35), "green": (110, 235, 70), "blue": (45, 95, 245), "purple": (150, 60, 215),
                 "purple_mini": (175, 90, 235), "orange": (255, 140, 30), "yellow": (245, 215, 40),
                 "teal": (40, 215, 200), "pink": (255, 105, 180),
                 "violet": (190, 150, 255)}
effects = []

def spawn_teleport_flash(from_x, from_y, to_x, to_y, color=(190, 130, 255)):
    """Burst of light at both ends of a teleport, with a streak of light between them."""
    for x, y in ((from_x, from_y), (to_x, to_y)):
        effects.append({"type": "flash", "x": x, "y": y, "age": 0.0, "life": 0.35, "color": color, "size": 1.3})
        for _ in range(14):
            angle = random.uniform(0, 2 * math.pi)
            speed = random.uniform(3, 9)
            effects.append({
                "type": "shard", "x": x, "y": y, "vx": math.cos(angle) * speed, "vy": math.sin(angle) * speed,
                "age": 0.0, "life": random.uniform(0.25, 0.45), "size": random.uniform(2, 5),
                "rot": random.uniform(0, 360), "spin": random.uniform(-25, 25),
                "color": random.choice([color, (255, 255, 255), (220, 190, 255)]), "sides": 4, "drag": 0.88,
            })
    effects.append({"type": "streak", "x": from_x, "y": from_y, "x2": to_x, "y2": to_y,
                    "age": 0.0, "life": 0.3, "color": color, "size": 1.0})

def spawn_death_effect(x, y, kind, color=None):
    """Burst something at world position (x, y) into spinning shards with a quick flash ring.
    Enemies shatter into small triangles; the player (kind "player", with its skin color) breaks
    into bigger, slower square chunks that fly further."""
    color = tuple(color[:3]) if color else EFFECT_COLORS[kind]
    is_player = kind == "player"
    size = 0.45 if kind == "purple_mini" else 1.6 if is_player else 1.0
    effects.append({"type": "flash", "x": x, "y": y, "age": 0.0, "life": 0.45 if is_player else 0.25, "color": color, "size": size})
    shades = [color, tuple(int(v * 0.5) for v in color), tuple(min(255, v + 90) for v in color)]
    for _ in range(int(16 * size) + 4):
        a = random.uniform(0, 2 * math.pi)
        speed = random.uniform(2, 7) * (0.5 + 0.5 * size)
        effects.append({
            "type": "shard", "x": x + math.cos(a) * 8 * size, "y": y + math.sin(a) * 8 * size,
            "vx": math.cos(a) * speed, "vy": math.sin(a) * speed, "age": 0.0,
            "life": random.uniform(0.9, 1.5) if is_player else random.uniform(0.35, 0.6),
            "size": random.uniform(3, 7) * size, "rot": random.uniform(0, 360), "spin": random.uniform(-20, 20),
            "color": random.choice(shades), "sides": 4 if is_player else 3, "drag": 0.94 if is_player else 0.9,
        })

def spawn_shot_clash(x, y):
    """Small purple-white spark where a player shot and an enemy shot destroy each other."""
    sounds.play("shot_clash")
    effects.append({"type": "flash", "x": x, "y": y, "age": 0.0, "life": 0.2, "color": (230, 150, 255), "size": 0.5})
    for _ in range(8):
        a = random.uniform(0, 2 * math.pi)
        speed = random.uniform(2, 5)
        effects.append({"type": "shard", "x": x, "y": y, "vx": math.cos(a) * speed, "vy": math.sin(a) * speed,
                        "age": 0.0, "life": random.uniform(0.2, 0.35), "size": random.uniform(2, 4),
                        "rot": random.uniform(0, 360), "spin": random.uniform(-20, 20),
                        "color": random.choice(((120, 190, 255), (255, 90, 80), (255, 255, 255))),
                        "sides": 3, "drag": 0.88})

def update_and_draw_effects(dt, paused, zoom=1.0):
    """Advance (unless paused) and draw all death effects, dropping the ones that have finished.
    zoom < 1 draws them zoomed out around the screen center (used by the game-over screen)."""
    if not paused:
        for fx in effects:
            fx["age"] += dt
            if fx["type"] == "shard":
                fx["x"] += fx["vx"]
                fx["y"] += fx["vy"]
                fx["vx"] *= fx["drag"]
                fx["vy"] *= fx["drag"]
                fx["rot"] += fx["spin"]
    effects[:] = [fx for fx in effects if fx["age"] < fx["life"]]
    for fx in effects:
        t = fx["age"] / fx["life"]
        sx, sy = world_to_screen(fx["x"], fx["y"], zoom)
        if fx["type"] != "streak" and not on_screen(sx, sy, 90):
            continue  # Off screen: still ages and moves above, just isn't drawn
        if fx["type"] == "streak":
            # The line of light left behind by a teleport
            start = world_to_screen(fx["x"], fx["y"], zoom)
            end = world_to_screen(fx["x2"], fx["y2"], zoom)
            fade = int(220 * (1 - t))
            layer = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
            pygame.draw.line(layer, (*fx["color"], fade // 3), start, end, int(14 * (1 - t) * zoom) + 2)
            pygame.draw.line(layer, (255, 255, 255, fade), start, end, int(5 * (1 - t) * zoom) + 1)
            screen.blit(layer, (0, 0))
        elif fx["type"] == "flash":
            radius = int((12 + 34 * t) * fx["size"] * zoom) + 2
            c = radius + 2
            surf = pygame.Surface((c * 2, c * 2), pygame.SRCALPHA)
            pygame.draw.circle(surf, (*fx["color"], int(220 * (1 - t))), (c, c), radius, max(2, int(6 * (1 - t))))
            pygame.draw.circle(surf, (255, 255, 255, int(230 * (1 - t) ** 2)), (c, c), max(1, int(radius * 0.6 * (1 - t))))
            screen.blit(surf, (sx - c, sy - c))
        else:
            size = fx["size"] * (1 - 0.7 * t) * zoom
            a = math.radians(fx["rot"])
            sides = fx["sides"]
            points = [(sx + math.cos(a + k * 2 * math.pi / sides) * size, sy + math.sin(a + k * 2 * math.pi / sides) * size) for k in range(sides)]
            pygame.draw.polygon(screen, fx["color"], points)

# Coins pop out of defeated enemies, hop, and bounce to a stop (z = height above the ground)
coin_orb = create_orb_sprite((255, 205, 40), coin_radius, glow=5)
coin_shadow = create_shadow_sprite(coin_radius)

def drop_coin(x, y):
    """Pop a coin out of a defeated enemy at world position (x, y) in a random direction."""
    a = random.uniform(0, 2 * math.pi)
    speed = random.uniform(1.0, 2.5)
    coins.append({"x": x, "y": y, "vx": math.cos(a) * speed, "vy": math.sin(a) * speed, "z": 0.0, "vz": 7.0})

def update_coin_bounce(coin):
    """Move a freshly dropped coin along its hop until it settles on the ground."""
    if coin.get("vz", 0) == 0 and coin.get("z", 0) == 0:
        return
    coin["x"] += coin["vx"]
    coin["y"] += coin["vy"]
    coin["z"] += coin["vz"]
    coin["vz"] -= 0.7  # Gravity
    if coin["z"] <= 0:
        coin["z"] = 0.0
        if coin["vz"] < -2.5:
            coin["vz"] = -coin["vz"] * 0.4  # Bounce
            coin["vx"] *= 0.5
            coin["vy"] *= 0.5
        else:
            coin["vz"] = coin["vx"] = coin["vy"] = 0.0

def enemy_killed(ex, ey, kind):
    """Burst a defeated enemy (top-left world position ex, ey) into pieces and pop out its coin."""
    cx, cy = ex + player_size // 2, ey + player_size // 2
    spawn_death_effect(cx, cy, kind)
    sounds.play("enemy_death")
    role = net_role()
    if role == "guest":
        recent_local_kills.append((kind, ex, ey, time.monotonic()))  # Coin and points come from the host
        return
    if role == "host":
        net_events.append(["kill", round(cx, 1), round(cy, 1), kind])
    if not in_shooting_range:
        drop_coin(cx, cy)
    if in_block_defence:
        globals()["block_defence_points"] += 1  # Shared by the whole team

# ---- Game over sequence ----
death_snapshot = None  # Picture of the world (no HUD, no player) taken the moment the player dies
death_time = 0.0

def ease_out_back(t):
    """0 -> 1 with a small overshoot at the end, for things that slide in and 'land'."""
    c1 = 1.70158
    return 1 + (c1 + 1) * (t - 1) ** 3 + c1 * (t - 1) ** 2

def ease_in_cubic(t):
    return t ** 3

def game_over_zoom():
    """Camera zoom during game over: slowly eases from 1.0 out to 0.9."""
    t = min(1.0, (pygame.time.get_ticks() / 1000 - death_time) / 3.0)
    return 1.0 - 0.1 * (1 - (1 - t) ** 3)

def on_screen(sx, sy, margin=80):
    """True if a screen position (plus a margin for its size/glow) is inside the window. Anything else is skipped when drawing."""
    return -margin < sx < WIDTH + margin and -margin < sy < HEIGHT + margin

barrier_layers = {}  # Reused full-screen layers for the barrier (making new ones every frame was slow)

def world_to_screen(wx, wy, zoom=1.0):
    """World position -> screen position, zooming around the center of the screen."""
    return (WIDTH / 2 + (wx - camera_x - WIDTH / 2) * zoom, HEIGHT / 2 + (wy - camera_y - HEIGHT / 2) * zoom)

def draw_world_background(zoom=1.0):
    """Endless grass, with the energy-grid barrier drawn over everything outside the playable map.
    The grass keeps going past the barrier so the world never seems to end - you just can't go there."""
    # Grass tiles, scaled for the zoom and lined up with the world
    ground = MAP_TEXTURES.get(selected_map, grass_texture)  # Grass, Snow or Sand
    step = ground.get_width() * zoom
    tile = ground if zoom == 1.0 else pygame.transform.smoothscale(ground, (math.ceil(step), math.ceil(step)))
    origin_x, origin_y = world_to_screen(0, 0, zoom)
    x = origin_x - math.ceil(origin_x / step) * step
    while x < WIDTH:
        y = origin_y - math.ceil(origin_y / step) * step
        while y < HEIGHT:
            screen.blit(tile, (math.floor(x), math.floor(y)))
            y += step
        x += step

    # Playable map in screen coordinates (Storm Survival shrinks it around the original map center)
    if in_storm_survival:
        left = MAP_WIDTH // 2 - storm_survival_map_width // 2
        top = MAP_HEIGHT // 2 - storm_survival_map_height // 2
        right = MAP_WIDTH // 2 + storm_survival_map_width // 2
        bottom = MAP_HEIGHT // 2 + storm_survival_map_height // 2
    else:
        left, top, right, bottom = 0, 0, MAP_WIDTH, MAP_HEIGHT
    screen_left, screen_top = world_to_screen(left, top, zoom)
    screen_right, screen_bottom = world_to_screen(right, bottom, zoom)
    map_rect = pygame.Rect(round(screen_left), round(screen_top), round(screen_right - screen_left), round(screen_bottom - screen_top))
    if map_rect.inflate(-40, -40).contains(screen.get_rect()):
        return  # The barrier (and its glow) is completely off screen, so there's nothing to draw

    # Energy barrier: a light red tint (the grass still shows through) with a pulsing grid on top
    ticks = pygame.time.get_ticks()
    pulse = (math.sin(ticks / 250) + 1) / 2  # 0..1
    if "grid" not in barrier_layers:
        barrier_layers["grid"] = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
        barrier_layers["glow"] = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    barrier_surface = barrier_layers["grid"]
    barrier_surface.fill((40, 0, 0, 70))
    grid_size = 40
    minor_color = (255, 40, 40, int(90 + 40 * pulse))
    major_color = (255, 90, 90, int(170 + 60 * pulse))
    # Grid lines are anchored to the world so they scroll with the camera; every 4th line is brighter
    view_half_w, view_half_h = WIDTH / 2 / zoom, HEIGHT / 2 / zoom
    first_col = math.floor((camera_x + WIDTH / 2 - view_half_w) / grid_size)
    last_col = math.ceil((camera_x + WIDTH / 2 + view_half_w) / grid_size)
    for k in range(first_col, last_col + 1):
        x = world_to_screen(k * grid_size, 0, zoom)[0]
        major = k % 4 == 0
        pygame.draw.line(barrier_surface, major_color if major else minor_color, (x, 0), (x, HEIGHT), 2 if major else 1)
    first_row = math.floor((camera_y + HEIGHT / 2 - view_half_h) / grid_size)
    last_row = math.ceil((camera_y + HEIGHT / 2 + view_half_h) / grid_size)
    for k in range(first_row, last_row + 1):
        y = world_to_screen(0, k * grid_size, zoom)[1]
        major = k % 4 == 0
        pygame.draw.line(barrier_surface, major_color if major else minor_color, (0, y), (WIDTH, y), 2 if major else 1)
    # A bright scan line sweeps down through the grid
    scan_y = ticks // 4 % (HEIGHT + 200) - 100
    pygame.draw.line(barrier_surface, (255, 80, 80, 60), (0, scan_y), (WIDTH, scan_y), 10)
    pygame.draw.line(barrier_surface, (255, 180, 180, 160), (0, scan_y), (WIDTH, scan_y), 2)
    # Keep the playable area clear
    barrier_surface.fill((0, 0, 0, 0), map_rect)
    # Glowing wall centered on the map edge: wide faint glow down to a bright core.
    # Drawn on its own layer and blended on top, so it brightens the grid instead of replacing it.
    glow_surface = barrier_layers["glow"]
    glow_surface.fill((0, 0, 0, 0))
    for glow_width, alpha in ((30, 50), (20, 90), (12, 160)):
        pygame.draw.rect(glow_surface, (255, 40, 40, int(alpha * (0.7 + 0.3 * pulse))), map_rect.inflate(glow_width, glow_width), glow_width)
    pygame.draw.rect(glow_surface, (255, 200, 200, 255), map_rect.inflate(4, 4), 4)
    barrier_surface.blit(glow_surface, (0, 0))
    screen.blit(barrier_surface, (0, 0))

def create_skull_icon(size=26):
    """Little white skull for the kills counter."""
    surf = pygame.Surface((size, size), pygame.SRCALPHA)
    c = size / 2
    bone, dark = (240, 240, 232), (30, 30, 36)
    head = pygame.Rect(0, 0, round(size * 0.84), round(size * 0.7))
    head.midtop = (round(c), 1)
    pygame.draw.ellipse(surf, bone, head)
    jaw = pygame.Rect(0, 0, round(size * 0.5), round(size * 0.32))
    jaw.midtop = (round(c), head.bottom - round(size * 0.14))
    pygame.draw.rect(surf, bone, jaw, border_radius=3)
    for side in (-1, 1):  # Eye sockets
        pygame.draw.circle(surf, dark, (c + side * size * 0.19, head.centery + 1), size * 0.13)
    nose_y = head.centery + size * 0.13
    pygame.draw.polygon(surf, dark, [(c, nose_y), (c - 2.5, nose_y + 4), (c + 2.5, nose_y + 4)])
    for offset in (-0.12, 0.0, 0.12):  # Gaps between the teeth
        pygame.draw.line(surf, dark, (c + offset * size, jaw.y + 3), (c + offset * size, jaw.bottom - 2), 1)
    return surf

def create_clock_icon(size=26):
    """Little clock for the time counter."""
    surf = pygame.Surface((size, size), pygame.SRCALPHA)
    c = size / 2
    r = size / 2 - 1
    pygame.draw.circle(surf, (235, 240, 248), (c, c), r)
    pygame.draw.circle(surf, (60, 150, 255), (c, c), r, 3)
    for i in range(12):  # Hour marks
        a = i * math.pi / 6
        pygame.draw.circle(surf, (70, 80, 95), (c + math.cos(a) * (r - 5), c + math.sin(a) * (r - 5)), 1)
    pygame.draw.line(surf, (30, 30, 36), (c, c), (c, c - r * 0.58), 2)              # Minute hand
    pygame.draw.line(surf, (30, 30, 36), (c, c), (c + r * 0.42, c + r * 0.12), 2)  # Hour hand
    pygame.draw.circle(surf, (220, 60, 60), (c, c), 2)
    return surf

def create_enemy_icon(size=26):
    """Little red enemy (orb with its visor) for the enemy counter."""
    surf = pygame.Surface((size, size), pygame.SRCALPHA)
    orb = create_orb_sprite((225, 35, 35), size // 2 - 2, glow=2)
    surf.blit(orb, orb.get_rect(center=(size // 2, size // 2)))
    visor = pygame.Rect(0, 0, round(size * 0.5), 5)
    visor.center = (size // 2, size // 2 - 1)
    pygame.draw.rect(surf, (20, 20, 26), visor, border_radius=2)
    pygame.draw.line(surf, (255, 120, 110), (visor.x + 3, visor.centery), (visor.right - 4, visor.centery), 1)
    return surf

STAT_ICONS = {"kills": create_skull_icon(), "coins": create_orb_sprite((255, 205, 40), 10, glow=3),
              "time": create_clock_icon(), "enemies": create_enemy_icon()}

def draw_stats_bar(stats):
    """Kills, coins and time side by side in one rounded bar under the minimap.
    stats is a list of (icon name, text, colour)."""
    gap, pad, icon_gap = 20, 16, 7
    pieces = [(STAT_ICONS.get(kind, pygame.Surface((0, 0))), coin_font.render(value, True, color)) for kind, value, color in stats]
    content_width = sum(icon.get_width() + icon_gap + text.get_width() for icon, text in pieces) + gap * (len(pieces) - 1)
    bar = pygame.Rect(0, 0, max(content_width + pad * 2, MINIMAP_RECT.width), 44)
    bar.topright = (MINIMAP_RECT.right, MINIMAP_RECT.bottom + 14)
    draw_panel(bar, radius=22)
    x = bar.centerx - content_width // 2
    for icon, text in pieces:
        screen.blit(icon, icon.get_rect(midleft=(x, bar.centery)))
        x += icon.get_width() + icon_gap
        screen.blit(text, text.get_rect(midleft=(x, bar.centery)))
        x += text.get_width() + gap

def blit_hud(text_surface, pos):
    """Blit HUD text with a dark drop shadow so it stays readable on bright maps like Snow and Sand."""
    shadow = text_surface.copy()
    shadow.fill((0, 0, 0, 255), special_flags=pygame.BLEND_RGBA_MIN)  # Same shape, all black
    shadow.set_alpha(190)
    screen.blit(shadow, (pos[0] + 2, pos[1] + 2))
    screen.blit(text_surface, pos)

def draw_text_with_shadow(text, text_font, color, center):
    """Text with a soft dark drop shadow so it stays readable over the busy game world."""
    shadow = text_font.render(text, True, (0, 0, 0))
    shadow.set_alpha(170)
    label = text_font.render(text, True, color)
    rect = label.get_rect(center=center)
    screen.blit(shadow, rect.move(2, 3))
    screen.blit(label, rect)

bubble_cache = {}

def get_bubble_text(text, size, top_color, bottom_color, outline=9):
    """create_bubble_text, cached, so text that changes (like the wave number) is only built once."""
    key = (text, size, top_color, bottom_color, outline)
    if key not in bubble_cache:
        bubble_cache[key] = create_bubble_text(text, size, top_color, bottom_color, outline=outline)
    return bubble_cache[key]

game_over_title = create_bubble_text("GAME OVER", 110, (255, 130, 110), (200, 20, 30))

def game_button_rects():
    """Bottom-left buttons for the current mode: (name, rect, colour, font). Quit, Exit and Pause
    are gone from the HUD - they live in the pause menu (Escape) now."""
    labels = []
    if in_shooting_range:
        labels = [("Add Enemies", GREEN, smaller_button_font, 150)]
    buttons, x = [], 20
    for name, color, label_font, width in labels:
        buttons.append((name, pygame.Rect(x, HEIGHT - 60, width, 40), color, label_font))
        x += width + 20
    return buttons

def draw_game_buttons():
    for name, rect, color, label_font in game_button_rects():
        draw_button(rect, color)
        text = label_font.render(name, True, BLACK)
        screen.blit(text, text.get_rect(center=rect.center))

# ---- Shops ----
SKIN_PRICES = {"white": 0, "black": 0, "rainbow": 1200, "galaxy": 1500, "lava": 1500, "water": 1500}  # Basic colours cost 800
SKIN_CARD_W, SKIN_CARD_H, SKIN_CARD_GAP, SKIN_COLUMNS = 220, 250, 26, 4

def card_rects(i, viewport, scroll):
    """Card and button rectangles for item i in a 4-column card grid inside `viewport`, scrolled by `scroll` px.
    Used by the hub's Shop, Upgrades, Abilities and Locker tabs."""
    col, row = i % SKIN_COLUMNS, i // SKIN_COLUMNS
    grid_w = SKIN_COLUMNS * SKIN_CARD_W + (SKIN_COLUMNS - 1) * SKIN_CARD_GAP
    card = pygame.Rect((WIDTH - grid_w) // 2 + col * (SKIN_CARD_W + SKIN_CARD_GAP),
                       viewport.y + 20 + row * (SKIN_CARD_H + SKIN_CARD_GAP) - round(scroll),
                       SKIN_CARD_W, SKIN_CARD_H)
    button = pygame.Rect(card.x + 20, card.bottom - 62, card.width - 40, 44)
    return card, button

def max_card_scroll(count, viewport):
    """How far a grid of `count` cards can scroll inside `viewport` (0 if it all fits)."""
    rows = math.ceil(count / SKIN_COLUMNS)
    content_h = 20 + rows * (SKIN_CARD_H + SKIN_CARD_GAP) - SKIN_CARD_GAP + 20
    return max(0, content_h - viewport.height)

def draw_panel(rect, highlight=False, radius=16):
    """Dark see-through rounded panel with a light border (green and thicker when highlighted)."""
    panel = pygame.Surface(rect.size, pygame.SRCALPHA)
    pygame.draw.rect(panel, (15, 18, 24, 175), panel.get_rect(), border_radius=radius)
    if highlight:
        pygame.draw.rect(panel, (120, 230, 140, 255), panel.get_rect(), 3, border_radius=radius)
    else:
        pygame.draw.rect(panel, (170, 175, 182, 130), panel.get_rect(), 2, border_radius=radius)
    screen.blit(panel, rect.topleft)

def draw_shop_header(title, coins_value):
    """Bubble-letter shop title plus a coin counter in the top right (coins_value None = everything is free)."""
    title_surface = get_bubble_text(title, 76, (255, 240, 150), (255, 160, 40))
    screen.blit(title_surface, (WIDTH // 2 - title_surface.get_width() // 2, 8))
    label = coin_font.render("Free" if coins_value is None else str(coins_value), True, (255, 230, 120))
    pill = pygame.Rect(0, 0, label.get_width() + 60, 44)
    pill.topright = (WIDTH - 20, 20)
    draw_panel(pill, radius=22)
    draw_orb(coin_orb, None, pill.x + 24, pill.centery)
    screen.blit(label, label.get_rect(midleft=(pill.x + 42, pill.centery)))

# Barrier Shrink countdown font: Bahnschrift has a techy, digital-display look (ships with Windows)
if "bahnschrift" in pygame.font.get_fonts():
    timer_font = pygame.font.SysFont("bahnschrift", 58, bold=True)
    ability_badge_font = pygame.font.SysFont("bahnschrift", 34, bold=True)
else:
    timer_font = pygame.font.SysFont(None, 72, bold=True)
    ability_badge_font = pygame.font.SysFont(None, 40, bold=True)

def draw_storm_timer(seconds_left):
    """Barrier Shrink countdown: glowing red digits in a dark tab hanging from the top-center of the screen.
    The tab is wider at the top than the bottom; in the last 30 seconds the red pulses faster."""
    top_w, bottom_w, h = 300, 230, 80
    cx = WIDTH // 2
    urgent = seconds_left <= 30
    pulse = (math.sin(pygame.time.get_ticks() / (120 if urgent else 300)) + 1) / 2
    points = [(cx - top_w // 2, -4), (cx + top_w // 2, -4), (cx + bottom_w // 2, h), (cx - bottom_w // 2, h)]
    # Soft red glow around the tab (on its own layer so it blends)
    glow_x = cx - top_w // 2 - 20
    glow = pygame.Surface((top_w + 40, h + 30), pygame.SRCALPHA)
    local_points = [(x - glow_x, y) for x, y in points]
    for width, alpha in ((14, 40), (8, 80)):
        pygame.draw.polygon(glow, (255, 30, 30, int(alpha * (0.7 + 0.3 * pulse))), local_points, width)
    screen.blit(glow, (glow_x, 0))
    # The tab is filled with the same red energy grid as the barrier, cut to the tab's shape
    grid_fill = pygame.Surface((WIDTH, h + 8), pygame.SRCALPHA)
    grid_fill.fill((40, 0, 0, 215))
    grid_size = 20
    minor_color = (255, 50, 50, int(70 + 40 * pulse))
    major_color = (255, 110, 110, int(150 + 60 * pulse))
    for x in range(0, WIDTH + grid_size, grid_size):
        major = (x // grid_size) % 4 == 0
        pygame.draw.line(grid_fill, major_color if major else minor_color, (x, 0), (x, h + 8), 2 if major else 1)
    for y in range(0, h + 8 + grid_size, grid_size):
        major = (y // grid_size) % 4 == 0
        pygame.draw.line(grid_fill, major_color if major else minor_color, (0, y), (WIDTH, y), 2 if major else 1)
    tab_mask = pygame.Surface((WIDTH, h + 8), pygame.SRCALPHA)
    pygame.draw.polygon(tab_mask, (255, 255, 255, 255), points)
    grid_fill.blit(tab_mask, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
    screen.blit(grid_fill, (0, 0))
    pygame.draw.polygon(screen, (255, 60, 60), points, 3)
    # Time remaining, with a red glow behind the digits
    text = f"{seconds_left // 60}:{seconds_left % 60:02d}"
    color = (255, int(50 + 70 * pulse), int(50 + 50 * pulse)) if urgent else (255, 70, 70)
    center = (cx, h // 2 - 2)
    halo = timer_font.render(text, True, (255, 0, 0))
    halo.set_alpha(70)
    for dx, dy in ((-2, 0), (2, 0), (0, -2), (0, 2)):
        screen.blit(halo, halo.get_rect(center=(center[0] + dx, center[1] + dy)))
    label = timer_font.render(text, True, color)
    screen.blit(label, label.get_rect(center=center))

# ---- Ability cooldown badge (slides down from the top of the screen) ----
ability_badge_anim = 0.0          # 0 = hidden above the screen, 1 = fully down
ability_badge_ready_timer = 0.0   # Keeps "READY" on screen for a moment once a cooldown ends
ABILITY_DURATION_VARS = {"shield": "shield_max_duration"}  # The rest follow the <key>_duration pattern

def ability_status():
    """(name, colour, seconds left, bar fraction, state) for the equipped ability, or None.
    state is "active" while it is running, "cooldown" while it recharges, or "ready"."""
    key = equipped_ability
    g = globals()
    if not key or not g.get("has_" + key):
        return None
    entry = next((e for e in ABILITIES if e[0] == key), None)
    if entry is None:
        return None
    _, name, color, _ = entry
    if g.get(key + "_active"):
        duration = g.get(ABILITY_DURATION_VARS.get(key, key + "_duration"), 1.0) or 1.0
        left = max(0.0, duration - g.get(key + "_timer", 0.0))
        return name, color, left, max(0.0, min(1.0, left / duration)), "active"
    cooldown = g.get(key + "_cooldown", 0.0)
    if cooldown > 0:
        full = g.get(key + "_cooldown_time", 1.0) or 1.0
        return name, color, cooldown, max(0.0, min(1.0, 1 - cooldown / full)), "cooldown"
    return name, color, 0.0, 1.0, "ready"

def draw_ability_badge(dt):
    """Cooldown/duration badge at the top middle: slides down while it matters, then slides back up."""
    global ability_badge_anim, ability_badge_ready_timer
    status = ability_status()
    showing = False
    if status:
        state = status[4]
        if state in ("active", "cooldown"):
            showing = True
            ability_badge_ready_timer = 1.2
        elif ability_badge_ready_timer > 0:
            ability_badge_ready_timer -= dt
            showing = ability_badge_ready_timer > 0
    ability_badge_anim += ((1.0 if showing else 0.0) - ability_badge_anim) * min(1.0, dt * 12)
    if status is None or ability_badge_anim < 0.02:
        return
    name, color, left, fraction, state = status
    width, height = 300, 66
    resting_y = 96 if in_storm_survival or active_boss is not None else 12  # Below the timer tab / boss bar
    if wave_completion_timer > 0:
        resting_y += 190  # Let the Wave Complete banner have the top of the screen
    if console_open:
        resting_y += 90  # And the console bar
    rect = pygame.Rect(WIDTH // 2 - width // 2, -height + (height + resting_y) * ability_badge_anim, width, height)
    panel = pygame.Surface((width, height), pygame.SRCALPHA)
    pygame.draw.rect(panel, (22, 25, 32, 235), panel.get_rect(), border_radius=14)
    pygame.draw.rect(panel, (*color, 220), panel.get_rect(), 3, border_radius=14)
    screen.blit(panel, rect.topleft)
    # Bar: fills up as the cooldown runs out, drains while the ability is running
    bar = pygame.Rect(rect.x + 14, rect.bottom - 17, rect.width - 28, 7)
    pygame.draw.rect(screen, (55, 60, 70), bar, border_radius=4)
    if fraction > 0:
        pygame.draw.rect(screen, color, (bar.x, bar.y, int(bar.width * fraction), bar.height), border_radius=4)
    label = smaller_button_font.render(name.upper(), True, (225, 230, 238))
    screen.blit(label, label.get_rect(midleft=(rect.x + 16, rect.y + 24)))
    if state == "ready":
        value_text, value_color = "READY", (140, 255, 170)
    elif state == "active":
        value_text, value_color = f"{left:.1f}s", (255, 255, 255)
    else:
        value_text, value_color = f"{left:.1f}s", color
    value = ability_badge_font.render(value_text, True, value_color)
    screen.blit(value, value.get_rect(midright=(rect.right - 16, rect.y + 24)))

# ---- Freeze ability visuals ----
def _frost_branch(surf, x, y, angle, length, depth, rng):
    """One ice crystal: a line that splits into smaller side branches."""
    end_x, end_y = x + math.cos(angle) * length, y + math.sin(angle) * length
    pygame.draw.line(surf, (240, 250, 255, 120 + depth * 30), (x, y), (end_x, end_y), max(1, depth))
    if depth > 1:
        for side in (-1, 1):
            along = rng.uniform(0.35, 0.75)
            _frost_branch(surf, x + (end_x - x) * along, y + (end_y - y) * along,
                          angle + side * rng.uniform(0.5, 0.9), length * rng.uniform(0.35, 0.55), depth - 1, rng)

def create_frost_overlay(width, height):
    """Frozen screen: a cold blue tint that thickens into white frost at the edges, with ice crystals
    growing in from every border. Built once, then faded in and out while Freeze is on."""
    rng = random.Random(21)
    surf = pygame.Surface((width, height), pygame.SRCALPHA)
    surf.fill((140, 200, 255, 40))
    edge = 170
    for i in range(edge):
        alpha = int(170 * (1 - i / edge) ** 2.2)
        pygame.draw.rect(surf, (225, 242, 255, max(40, alpha)), (i, i, width - 2 * i, height - 2 * i), 1)
    for _ in range(90):
        side = rng.randrange(4)
        if side == 0:
            x, y, angle = rng.uniform(0, width), 0, math.pi / 2
        elif side == 1:
            x, y, angle = rng.uniform(0, width), height, -math.pi / 2
        elif side == 2:
            x, y, angle = 0, rng.uniform(0, height), 0.0
        else:
            x, y, angle = width, rng.uniform(0, height), math.pi
        _frost_branch(surf, x, y, angle + rng.uniform(-0.6, 0.6), rng.uniform(45, 160), 3, rng)
    for _ in range(140):  # Glittering specks of frost
        side = rng.randrange(4)
        x = rng.uniform(0, width) if side < 2 else rng.uniform(0, 120) if side == 2 else rng.uniform(width - 120, width)
        y = rng.uniform(0, 120) if side == 0 else rng.uniform(height - 120, height) if side == 1 else rng.uniform(0, height)
        pygame.draw.circle(surf, (255, 255, 255, rng.randint(120, 230)), (x, y), rng.choice((1, 1, 2)))
    return surf

FROST_OVERLAY = create_frost_overlay(WIDTH, HEIGHT)

def draw_ice_block(cx, cy, size, crack, seed):
    """A translucent block of ice over a frozen enemy. crack (0..1) adds more and longer cracks; the
    seed keeps each block's cracks in the same place from frame to frame."""
    pad = 4
    surf = pygame.Surface((size + pad * 2, size + pad * 2), pygame.SRCALPHA)
    block = pygame.Rect(pad, pad, size, size)
    pygame.draw.rect(surf, (175, 225, 255, 125), block, border_radius=7)
    pygame.draw.rect(surf, (225, 245, 255, 70), (block.x, block.y, size, int(size * 0.35)),
                     border_top_left_radius=7, border_top_right_radius=7)
    pygame.draw.polygon(surf, (255, 255, 255, 150), [(block.x + 6, block.y + 6), (block.x + size * 0.45, block.y + 6),
                                                    (block.x + 6, block.y + size * 0.45)])
    pygame.draw.rect(surf, (230, 248, 255, 230), block, 2, border_radius=7)
    if crack > 0:
        rng = random.Random(seed)
        for _ in range(1 + int(crack * 5)):
            x = block.x + rng.uniform(size * 0.25, size * 0.75)
            y = block.y + rng.uniform(size * 0.25, size * 0.75)
            angle = rng.uniform(0, 2 * math.pi)
            reach = size * (0.2 + 0.45 * crack) * rng.uniform(0.7, 1.0)
            points = [(x, y)]
            for _ in range(3):
                angle += rng.uniform(-0.7, 0.7)
                x += math.cos(angle) * reach / 3
                y += math.sin(angle) * reach / 3
                points.append((x, y))
            pygame.draw.lines(surf, (255, 255, 255, 235), False, points, 2)
    screen.blit(surf, (cx - size / 2 - pad, cy - size / 2 - pad))

def draw_frozen_world():
    """Freeze: every enemy locked in ice that cracks as time runs out, and the whole screen frosted over."""
    progress = min(1.0, freeze_timer / freeze_duration)
    crack = max(0.0, (progress - 0.45) / 0.55)  # Starts cracking a little before halfway
    half = player_size // 2
    for group in (red_enemies, green_enemies, blue_enemies, purple_enemies):
        for ex, ey in group:
            draw_ice_block(ex - camera_x + half, ey - camera_y + half, player_size + 18, crack, int(ex) * 7919 + int(ey))
    for enemy in orange_enemies + yellow_enemies + teal_enemies + pink_enemies + violet_enemies:
        draw_ice_block(enemy["x"] - camera_x + half, enemy["y"] - camera_y + half, player_size + 18, crack,
                       int(enemy["x"]) * 7919 + int(enemy["y"]))
    for minis in purple_mini_circles:
        for mini_x, mini_y, _ in minis:
            draw_ice_block(mini_x - camera_x, mini_y - camera_y, purple_mini_size + 10, crack, int(mini_x) * 31 + int(mini_y))
    # Frost rushes in, then melts away over the last half second
    fade = min(1.0, freeze_timer / 0.3, (freeze_duration - freeze_timer) / 0.5)
    FROST_OVERLAY.set_alpha(int(255 * max(0.0, fade)))
    screen.blit(FROST_OVERLAY, (0, 0))

# ---- Shield: a curved energy plate held out on the gun side ----
SHIELD_ARC = math.radians(110)  # How much of a circle the shield covers
SHIELD_RADIUS = 66              # Distance from the player's centre to the middle of the plate
SHIELD_THICKNESS = 16

def shield_blocks(wx, wy, extra=0):
    """Is something at world position (wx, wy), with radius `extra`, touching the shield in front of the player?"""
    dx = wx - (player_x + player_size / 2)
    dy = wy - (player_y + player_size / 2)
    distance = math.hypot(dx, dy)
    if not SHIELD_RADIUS - SHIELD_THICKNESS - extra <= distance <= SHIELD_RADIUS + SHIELD_THICKNESS + extra:
        return False
    off_centre = (math.atan2(dy, dx) - last_rot_angle + math.pi) % (2 * math.pi) - math.pi
    return abs(off_centre) <= SHIELD_ARC / 2 + extra / max(distance, 1)

def draw_shield():
    """The shield: glowing plate with energy ribs and bright rims, a spark running along its edge,
    flickering as it is about to run out."""
    t = pygame.time.get_ticks() / 1000
    if shield_timer > shield_max_duration * 0.75 and int(t * 18) % 2:
        return  # Flicker when it is nearly spent
    pulse = (math.sin(t * 6) + 1) / 2
    size = int((SHIELD_RADIUS + SHIELD_THICKNESS + 24) * 2)
    c = size / 2
    surf = pygame.Surface((size, size), pygame.SRCALPHA)
    start = last_rot_angle - SHIELD_ARC / 2
    steps = 28

    def arc(radius):
        return [(c + math.cos(start + SHIELD_ARC * i / steps) * radius,
                 c + math.sin(start + SHIELD_ARC * i / steps) * radius) for i in range(steps + 1)]

    outer, inner = arc(SHIELD_RADIUS + SHIELD_THICKNESS / 2), arc(SHIELD_RADIUS - SHIELD_THICKNESS / 2)
    pygame.draw.polygon(surf, (80, 170, 255, int(45 + 35 * pulse)),
                        arc(SHIELD_RADIUS + SHIELD_THICKNESS / 2 + 12) + arc(SHIELD_RADIUS - SHIELD_THICKNESS / 2 - 8)[::-1])
    pygame.draw.polygon(surf, (90, 190, 255, 155), outer + inner[::-1])
    for i in range(2, steps - 1, 3):  # Energy ribs across the plate
        pygame.draw.line(surf, (205, 240, 255, 150), inner[i], outer[i], 2)
    pygame.draw.lines(surf, (235, 250, 255, 245), False, outer, 3)
    pygame.draw.lines(surf, (150, 220, 255, 210), False, inner, 2)
    spark = outer[int((t * 1.6) % 1.0 * steps)]
    pygame.draw.circle(surf, (120, 210, 255, 120), spark, 8)
    pygame.draw.circle(surf, (255, 255, 255, 240), spark, 4)
    screen.blit(surf, (player_x - camera_x + player_size / 2 - c, player_y - camera_y + player_size / 2 - c))

# ---- Accounts and saving ----
UPGRADE_FLAGS = ["has_gun_upgrade", "has_gun_upgrade_1", "has_gun_upgrade_2", "has_gun_upgrade_3",
                 "has_gun_upgrade_4", "has_gun_upgrade_5",
                 "has_magnet_1", "has_magnet_2", "has_magnet_3", "has_magnet_4", "has_magnet_5",
                 "has_shield", "has_teleport", "has_freeze",
                 "has_shockwave", "has_helpers", "has_coin_controller", "has_triple_bullet"]
# Abilities: key, display name, icon color, price
ABILITIES = [("freeze", "Freeze", (150, 220, 255), 1500), ("shield", "Shield", (90, 160, 255), 1500),
             ("teleport", "Teleport", (190, 120, 255), 1300), ("helpers", "Helpers", (255, 210, 90), 1800),
             ("shockwave", "Shockwave", (255, 140, 60), 2000),
             ("coin_controller", "Coin Controller", (255, 215, 40), 1300), ("triple_bullet", "Triple Bullet", (255, 90, 120), 1600)]
ABILITY_ICONS = {key: create_orb_sprite(color, 34, glow=8) for key, _, color, _ in ABILITIES}
DAILY_SKIN_POOL = [skin for skin in shop_skins if skin not in ("white", "black")]
GUN_SHOT_DELAYS = [0.5, 0.43, 0.36, 0.29, 0.22, 0.15]  # Time between shots for gun level 0-5 (5 = the old max)
MAGNET_RANGES = [0, 120, 140, 160, 180, 200]  # Coin pull distance for magnet level 0-5 (5 = the old max)

def gun_level():
    return sum(bool(globals()[f"has_gun_upgrade_{n}"]) for n in range(1, 6))

def magnet_level():
    return sum(bool(globals()[f"has_magnet_{n}"]) for n in range(1, 6))

best_wave = 0
# Online accounts (Supabase) work on every computer. Tests that point the game at a scratch save file stay offline.
ONLINE_ACCOUNTS = bool(os.environ.get("CUBE_SHOOTER_ONLINE")) or "CUBE_SHOOTER_SAVE" not in os.environ
online_session = None  # cube_online.Session while logged in to an online account
cloud_saver = cube_online.Saver() if ONLINE_ACCOUNTS else None
current_account = None  # Display name of the logged-in player (None = nobody is logged in)
save_data = cube_accounts.load_save()
last_saved_progress = None
last_save_time = 0.0

def sync_main_game_backup():
    """Copy the live skins/upgrades into the main-game copies. The game restores those copies when you
    leave the Shooting Range (where everything is free) and when you start Waves, so they must always
    hold your real progress - otherwise things bought in the game-over shops would be lost."""
    g = globals()
    for flag in UPGRADE_FLAGS:
        g["main_game_" + flag] = g[flag]
    g["main_game_owned_skins"] = dict(owned_skins)
    g["main_game_skin"] = current_skin
    g["main_game_equipped_ability"] = equipped_ability
    g["main_game_shot_delay"] = shot_delay

def progress_state():
    """Everything saved to the logged-in account. Uses the main-game copies, since the Shooting Range
    temporarily hands out free skins and upgrades."""
    g = globals()
    return {
        "coins": main_game_coins,
        "owned_skins": dict(main_game_owned_skins),
        "skin": main_game_skin,
        "upgrades": {flag: bool(g["main_game_" + flag]) for flag in UPGRADE_FLAGS},
        "equipped_ability": main_game_equipped_ability,
        "best_wave": best_wave,
        "map": selected_map,
    }

def apply_progress(progress):
    """Load an account's saved progress into the game (a brand-new account starts fresh)."""
    g = globals()
    g["coin_count"] = g["main_game_coins"] = int(progress.get("coins", 0))
    skins = {name: name in ("white", "black") for name in shop_skins}
    skins.update({name: bool(owned) for name, owned in progress.get("owned_skins", {}).items() if name in skins})
    g["owned_skins"] = skins
    g["main_game_owned_skins"] = dict(skins)
    skin = progress.get("skin", "white")
    g["current_skin"] = g["main_game_skin"] = skin if skins.get(skin) else "white"
    upgrades = progress.get("upgrades", {})
    for flag in UPGRADE_FLAGS:
        g[flag] = g["main_game_" + flag] = bool(upgrades.get(flag, False))
    ability = progress.get("equipped_ability")
    g["equipped_ability"] = g["main_game_equipped_ability"] = ability if ability and g.get("has_" + ability) else None
    g["shot_delay"] = g["main_game_shot_delay"] = GUN_SHOT_DELAYS[gun_level()]
    g["best_wave"] = int(progress.get("best_wave", 0))
    g["selected_map"] = progress.get("map") if progress.get("map") in MAP_NAMES else "Grass"

def update_progress_and_autosave():
    """Run every frame: keep coins and the main-game copies in sync, and save the logged-in account
    whenever its progress changes (at most once a second)."""
    global coin_count, main_game_coins, last_saved_progress, last_save_time
    if in_shooting_range:
        main_game_coins = coin_count = sandbox_entry_coins  # No free coins from the Sandbox
    if not in_shooting_range and not in_tutorial:  # Tutorial coins are practice only
        if not in_block_defence:
            # On menus coin_count can be left over from Block Defence, so the saved total wins there;
            # while playing (or in the game-over shops) the live count wins
            if start_screen or hub_open or settings_open:
                coin_count = main_game_coins
            else:
                main_game_coins = coin_count
        sync_main_game_backup()
    if current_account is None:
        return
    state = progress_state()
    now = time.time()
    if state != last_saved_progress and now - last_save_time >= 1.0:
        store_progress(state)
        last_saved_progress = state
        last_save_time = now

def store_progress(state, right_now=False):
    """Online accounts upload (in the background, or right away) and keep a local copy; local accounts write the save file."""
    if online_session is None:
        cube_accounts.save_progress(save_data, current_account, state)
        return
    synced = cloud_saver.flush(online_session, state) if right_now else None
    cube_accounts.cache_cloud_progress(save_data, online_session.user_id, current_account, state,
                                       unsynced=(synced is False) or (synced is None and cloud_saver.failed))
    if not right_now:
        cloud_saver.queue(online_session, state)

def save_current_account():
    """Save right away (when logging out, and when the game closes)."""
    global last_saved_progress, last_save_time
    if current_account is not None:
        last_saved_progress = progress_state()
        last_save_time = time.time()
        store_progress(last_saved_progress, right_now=True)

atexit.register(save_current_account)  # Also covers the Quit buttons, which exit straight away

# ---- Login screen ----
login_screen_open = True
login_fields = {"username": save_data["last_user"], "password": ""}
login_focus = "password" if save_data["last_user"] else "username"
login_message = ""
login_message_ok = False
LOGIN_PANEL = pygame.Rect(WIDTH // 2 - 250, 290, 500, 440)
LOGIN_REMEMBER_BOX = pygame.Rect(WIDTH // 2 - 200, 532, 26, 26)
login_remember = False
LOGIN_FIELD_RECTS = {"username": pygame.Rect(WIDTH // 2 - 200, 375, 400, 52),
                     "password": pygame.Rect(WIDTH // 2 - 200, 465, 400, 52)}
LOGIN_BUTTON = pygame.Rect(WIDTH // 2 - 200, 580, 190, 56)
CREATE_BUTTON = pygame.Rect(WIDTH // 2 + 10, 580, 190, 56)
LOGIN_QUIT_BUTTON = pygame.Rect(20, HEIGHT - 60, 100, 40)
LOGOUT_BUTTON = pygame.Rect(WIDTH - 140, 20, 120, 40)
login_title_cube = pygame.transform.smoothscale_by(title_cube_surface, 0.6)
login_title_shooter = pygame.transform.smoothscale_by(title_shooter_surface, 0.6)

def log_in_as(account, message):
    """Load an account and go to the main menu."""
    global current_account, login_screen_open, start_screen, last_saved_progress, last_save_time
    global console_message, console_message_timer
    apply_progress(account["progress"])
    current_account = account["name"]
    if online_session is not None:
        if login_remember:
            cube_accounts.remember_online(online_session.name, online_session.refresh_token)
            online_session.on_new_refresh_token = lambda token: cube_accounts.remember_online(current_account, token)
        else:
            cube_accounts.forget_remembered(save_data)
        if save_data.get("last_user") != account["name"]:
            save_data["last_user"] = account["name"]
            cube_accounts.write_save(save_data)
    elif login_remember:
        cube_accounts.remember_account(save_data, account["name"])
    else:
        cube_accounts.forget_remembered(save_data, account["name"])
    last_saved_progress = progress_state()
    last_save_time = time.time()
    login_fields["password"] = ""
    login_screen_open = False
    start_screen = True
    console_message, console_message_timer = message, 3.0  # "Welcome back, ...!" toast

def log_out():
    """Save and go back to the login screen."""
    global current_account, login_screen_open, login_focus, login_message, login_remember, online_session
    save_current_account()
    cube_accounts.forget_remembered(save_data, current_account)  # Logging out means log in again next time
    if online_session is not None:
        cube_online.log_out(online_session)
        online_session = None
    set_play_multiplayer(False)
    net.close()
    login_remember = False
    current_account = None
    login_fields["username"], login_fields["password"] = save_data["last_user"], ""
    login_focus = "password" if login_fields["username"] else "username"
    login_message = ""
    login_screen_open = True

def attempt_login():
    global login_message, login_message_ok
    if ONLINE_ACCOUNTS:
        return online_attempt(create=False)
    account, login_message = cube_accounts.check_login(save_data, login_fields["username"], login_fields["password"])
    login_message_ok = account is not None
    if account:
        log_in_as(account, login_message)

def attempt_create():
    global login_message, login_message_ok
    if ONLINE_ACCOUNTS:
        return online_attempt(create=True)
    account, login_message = cube_accounts.create_account(save_data, login_fields["username"], login_fields["password"])
    login_message_ok = account is not None
    if account:
        log_in_as(account, login_message)

def show_login_status(text):
    """Draw the login screen with a message right away (the server takes a moment to answer)."""
    global login_message, login_message_ok
    login_message, login_message_ok = text, True
    draw_login_screen()
    pygame.display.flip()

def newest_progress(session, server_progress):
    """If this PC holds progress that never reached the server (internet dropped), that copy is newer."""
    cached = save_data.get("cloud", {}).get(session.user_id)
    if cached and cached.get("unsynced"):
        cloud_saver.queue(session, cached["progress"])
        return cached["progress"]
    return server_progress

def online_attempt(create):
    """Log in to / create an online account. A local account from before accounts went online (same
    username and password) is moved online the first time, bringing its progress with it."""
    global login_message, login_message_ok, online_session
    name, password = login_fields["username"].strip(), login_fields["password"]
    if not 3 <= len(name) <= 16:
        login_message, login_message_ok = "Username must be 3-16 characters", False
        return
    if len(password) < 4:
        login_message, login_message_ok = "Password must be at least 4 characters", False
        return
    show_login_status("Creating account..." if create else "Logging in...")
    local = cube_accounts.local_account_matches(save_data, name, password)
    try:
        if create:
            session, progress = cube_online.sign_up(name, password, local["progress"] if local else None)
            message = f"Welcome, {session.name}!"
        else:
            try:
                session, progress = cube_online.log_in(name, password)
                progress = newest_progress(session, progress)
                message = f"Welcome back, {session.name}!"
            except cube_online.ServerError as err:
                if err.status != 400 or local is None:
                    raise
                # Not online yet, but this PC has that account: move it online
                session, progress = cube_online.sign_up(local["name"], password, local["progress"])
                message = f"Welcome back, {session.name}! Your account is online now"
        if local:
            cube_accounts.mark_moved_online(save_data, name)
    except cube_online.OfflineError:
        login_message, login_message_ok = "Can't reach the server - check your internet", False
        return
    except cube_online.ServerError as err:
        if err.status in (400, 409) and not create:  # 409: tried moving a local account but the name is taken online
            login_message = "Wrong username or password"
        elif err.status == 409:
            login_message = "That username is taken"
        elif err.status == 429:
            login_message = "Too many tries - wait a minute"
        else:
            login_message = "Server error: " + str(err)[:40]
        login_message_ok = False
        return
    online_session = session
    login_message_ok = True
    log_in_as({"name": session.name, "progress": progress}, message)

def draw_login_screen():
    screen.blit(metal_background, (0, 0))
    bob_time = pygame.time.get_ticks() / 500
    screen.blit(login_title_shooter, (WIDTH // 2 - login_title_shooter.get_width() // 2, 121 + math.sin(bob_time + 1.2) * 4))
    screen.blit(login_title_cube, (WIDTH // 2 - login_title_cube.get_width() // 2, 20 + math.sin(bob_time) * 4))
    draw_panel(LOGIN_PANEL)
    heading = coin_font.render("Log in or create an account", True, WHITE)
    screen.blit(heading, heading.get_rect(center=(WIDTH // 2, LOGIN_PANEL.y + 32)))
    for field, label in (("username", "Username"), ("password", "Password")):
        rect = LOGIN_FIELD_RECTS[field]
        label_text = small_button_font.render(label, True, (205, 210, 216))
        screen.blit(label_text, (rect.x, rect.y - 26))
        focused = login_focus == field
        pygame.draw.rect(screen, WHITE, rect, border_radius=8)
        pygame.draw.rect(screen, (255, 200, 60) if focused else (40, 40, 40), rect, 3 if focused else 2, border_radius=8)
        shown = login_fields[field] if field == "username" else "*" * len(login_fields[field])  # Hide the password
        text = button_font.render(shown, True, BLACK)
        visible_w = min(text.get_width(), rect.width - 24)  # Long text shows its end, like a normal text box
        screen.blit(text, (rect.x + 12, rect.centery - text.get_height() // 2),
                    pygame.Rect(text.get_width() - visible_w, 0, visible_w, text.get_height()))
        if focused and (pygame.time.get_ticks() // 500) % 2 == 0:
            cursor_x = rect.x + 14 + visible_w
            pygame.draw.line(screen, BLACK, (cursor_x, rect.y + 12), (cursor_x, rect.bottom - 12), 2)
    box = LOGIN_REMEMBER_BOX
    pygame.draw.rect(screen, WHITE, box, border_radius=5)
    pygame.draw.rect(screen, (255, 200, 60) if login_remember else (40, 40, 40), box, 2, border_radius=5)
    if login_remember:
        pygame.draw.lines(screen, (40, 150, 70), False,
                          [(box.x + 6, box.centery), (box.x + 11, box.bottom - 7), (box.right - 5, box.y + 6)], 4)
    remember_text = small_button_font.render("Remember me on this device", True, (205, 210, 216))
    screen.blit(remember_text, remember_text.get_rect(midleft=(box.right + 12, box.centery)))
    for rect, label, label_font in ((LOGIN_BUTTON, "Log In", button_font), (CREATE_BUTTON, "Create Account", small_button_font)):
        draw_button(rect, BLUE)
        text = label_font.render(label, True, BLACK)
        screen.blit(text, text.get_rect(center=rect.center))
    if login_message:
        message = coin_font.render(login_message, True, (120, 230, 140) if login_message_ok else (255, 110, 110))
        screen.blit(message, message.get_rect(center=(WIDTH // 2, LOGIN_PANEL.y + 378)))
    names = [] if ONLINE_ACCOUNTS else cube_accounts.account_names(save_data)
    if names:
        accounts_text = small_button_font.render("Accounts on this PC: " + ", ".join(names[:6]), True, (170, 175, 182))
        screen.blit(accounts_text, accounts_text.get_rect(center=(WIDTH // 2, LOGIN_PANEL.bottom + 25)))
    draw_button(LOGIN_QUIT_BUTTON, RED)
    quit_text = button_font.render("Quit", True, BLACK)
    screen.blit(quit_text, quit_text.get_rect(center=LOGIN_QUIT_BUTTON.center))
    hint = small_button_font.render("Tab = switch box    Enter = log in", True, (170, 175, 182))
    screen.blit(hint, hint.get_rect(center=(WIDTH // 2, HEIGHT - 40)))

def draw_update_status():
    """Small note in the bottom-left: the version, and what the auto-updater is doing."""
    if auto_updater.state == "downloading":
        text = f"Downloading update v{auto_updater.update.version}...  {int(auto_updater.progress * 100)}%"
        color = (140, 220, 255)
    elif auto_updater.state == "ready":
        text = f"Update v{auto_updater.update.version} ready - installs when you're on a menu"
        color = (140, 255, 170)
    elif auto_updater.state == "failed":
        text = f"v{VERSION}  (update failed - it will try again next time)"
        color = (255, 150, 140)
    else:
        text = f"v{VERSION}"
        color = (200, 205, 212)
    label = small_button_font.render(text, True, color)
    if auto_updater.state in ("downloading", "ready"):
        box = label.get_rect(bottomleft=(12, HEIGHT - 10)).inflate(16, 10)
        pygame.draw.rect(screen, (20, 24, 32), box, border_radius=8)
        if auto_updater.state == "downloading":
            bar = pygame.Rect(box.x + 6, box.bottom - 5, int((box.width - 12) * auto_updater.progress), 3)
            pygame.draw.rect(screen, color, bar)
    screen.blit(label, label.get_rect(bottomleft=(12, HEIGHT - 10)))

def login_screen_frame(events):
    """Handle input for the login screen and draw it."""
    global login_focus, running, login_remember
    for event in events:
        if event.type == pygame.QUIT:
            running = False
        elif event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
            pos = pygame.mouse.get_pos()
            for field, rect in LOGIN_FIELD_RECTS.items():
                if rect.collidepoint(pos):
                    login_focus = field
            if pygame.Rect(LOGIN_REMEMBER_BOX.x, LOGIN_REMEMBER_BOX.y - 4, 330, LOGIN_REMEMBER_BOX.height + 8).collidepoint(pos):
                login_remember = not login_remember  # The box or its label
            if LOGIN_BUTTON.collidepoint(pos):
                attempt_login()
            elif CREATE_BUTTON.collidepoint(pos):
                attempt_create()
            elif LOGIN_QUIT_BUTTON.collidepoint(pos):
                running = False
        elif event.type == pygame.KEYDOWN:
            if event.key == pygame.K_TAB:
                login_focus = "password" if login_focus == "username" else "username"
            elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                attempt_login()
            elif event.key == pygame.K_BACKSPACE:
                login_fields[login_focus] = login_fields[login_focus][:-1]
            elif event.key == pygame.K_F11:
                pygame.display.toggle_fullscreen()
            elif event.unicode and event.unicode.isprintable():
                limit = 16 if login_focus == "username" else 32
                if len(login_fields[login_focus]) < limit:
                    login_fields[login_focus] += event.unicode
        if not login_screen_open:
            break  # Logged in: the rest of this frame's input belongs to the main menu
    if login_screen_open:
        draw_login_screen()

# ---- Main menu ----
MAIN_MENU_BUTTONS = ["Play", "Settings", "Quit"]

def main_menu_buttons():
    return [(name, pygame.Rect(WIDTH // 2 - 120, 466 + i * 56, 240, 50)) for i, name in enumerate(MAIN_MENU_BUTTONS)]

# ---- Minimap (all game modes) - square, because the map is square ----
MINIMAP_SIZE = 176
MINIMAP_RECT = pygame.Rect(WIDTH - MINIMAP_SIZE - 22, 30, MINIMAP_SIZE, MINIMAP_SIZE)

def draw_minimap():
    """Square minimap in the top right: the whole map, the area you can still play in, enemies and you."""
    size = MINIMAP_SIZE
    scale = size / MAP_WIDTH
    surf = pygame.Surface((size, size), pygame.SRCALPHA)
    surf.fill((18, 26, 18, 210))
    # The playable area (Barrier Shrink shrinks it)
    if in_storm_survival:
        left = MAP_WIDTH // 2 - storm_survival_map_width // 2
        top = MAP_HEIGHT // 2 - storm_survival_map_height // 2
        width, height = storm_survival_map_width, storm_survival_map_height
    else:
        left, top, width, height = 0, 0, MAP_WIDTH, MAP_HEIGHT
    play_rect = pygame.Rect(left * scale, top * scale, width * scale, height * scale)
    pygame.draw.rect(surf, MINIMAP_GROUND.get(selected_map, MINIMAP_GROUND["Grass"]), play_rect)
    pygame.draw.rect(surf, (255, 70, 70, 230), play_rect, 2)
    if in_block_defence:
        block = BLOCK_DEFENCE_BLOCK_RECT
        pygame.draw.rect(surf, (150, 150, 150), (block.x * scale, block.y * scale,
                                                 max(3, block.width * scale), max(3, block.height * scale)))
    for group, color in ((red_enemies, (235, 60, 60)), (green_enemies, (120, 235, 80)),
                         (blue_enemies, (70, 120, 255)), (purple_enemies, (170, 90, 230))):
        for ex, ey in group:
            pygame.draw.circle(surf, color, ((ex + player_size // 2) * scale, (ey + player_size // 2) * scale), 3)
    for enemy in orange_enemies:
        pygame.draw.circle(surf, (255, 150, 40), ((enemy["x"] + player_size // 2) * scale, (enemy["y"] + player_size // 2) * scale), 3)
    if active_boss is not None and not (active_boss["kind"] == "teal" and not teal_boss_visible(active_boss)):
        pygame.draw.circle(surf, BOSSES[active_boss["kind"]]["minimap"], (active_boss["x"] * scale, active_boss["y"] * scale), max(6, BOSS_RADIUS * scale))
    for enemy in yellow_enemies:
        pygame.draw.circle(surf, (250, 225, 50), ((enemy["x"] + player_size // 2) * scale, (enemy["y"] + player_size // 2) * scale), 3)
    for enemy in violet_enemies:
        pygame.draw.circle(surf, (205, 175, 255), ((enemy["x"] + player_size // 2) * scale, (enemy["y"] + player_size // 2) * scale), 3)
    for enemy in pink_enemies:
        pygame.draw.circle(surf, (255, 130, 200), ((enemy["x"] + player_size // 2) * scale, (enemy["y"] + player_size // 2) * scale), 3)
    for enemy in teal_enemies:
        pygame.draw.circle(surf, (60, 230, 215), ((enemy["x"] + player_size // 2) * scale, (enemy["y"] + player_size // 2) * scale), 3)
    player_dot = ((player_x + player_size // 2) * scale, (player_y + player_size // 2) * scale)
    pygame.draw.circle(surf, (15, 15, 20), player_dot, 6)
    pygame.draw.circle(surf, WHITE, player_dot, 4)
    # Soften the corners, then frame it
    corner_mask = pygame.Surface((size, size), pygame.SRCALPHA)
    pygame.draw.rect(corner_mask, (255, 255, 255, 255), corner_mask.get_rect(), border_radius=10)
    surf.blit(corner_mask, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
    screen.blit(surf, MINIMAP_RECT.topleft)
    pygame.draw.rect(screen, (255, 80, 80), MINIMAP_RECT.inflate(4, 4), 3, border_radius=12)
    pygame.draw.rect(screen, (40, 44, 50), MINIMAP_RECT.inflate(10, 10), 2, border_radius=14)

# ---- Code console bar and admin panel ----
ADMIN_CODE = "8743841"
console_anim = 0.0        # 0 = hidden, 1 = fully dropped down
admin_code_open = False   # The "Enter code" box you get after typing admin
admin_code_input = ""
admin_panel_open = False
CONSOLE_BAR = pygame.Rect(WIDTH // 2 - 380, 0, 760, 74)
ADMIN_GIVE_BUTTON = pygame.Rect(WIDTH // 2 - 170, 420, 340, 60)
ADMIN_SHOP_BUTTON = pygame.Rect(WIDTH // 2 - 170, 492, 340, 60)
ADMIN_CLOSE_BUTTON = pygame.Rect(WIDTH // 2 - 170, 564, 340, 60)

def close_console_stack():
    """Close the console bar and any admin screen, and let the game run again."""
    global console_open, admin_code_open, admin_panel_open, console_input, admin_code_input, game_paused
    console_open = admin_code_open = admin_panel_open = False
    console_input = admin_code_input = ""
    game_paused = console_was_paused

wave_jump_pending = False  # Set by the wave# command so the next wave spawns without a reward or banner

def jump_to_wave(number):
    """wave# command: skip straight to that wave in a Waves game."""
    global wave, wave_jump_pending, console_message, console_message_timer
    in_waves_game = not (start_screen or hub_open or settings_open or game_over or in_shooting_range
                         or in_storm_survival or in_block_defence or in_tutorial)
    if not in_waves_game:
        console_message = "Start a Waves game first"
    else:
        wave = number - 1
        wave_jump_pending = True
        for group in (red_enemies, green_enemies, blue_enemies, blue_last_shot_times, blue_bullets,
                      purple_enemies, purple_mini_circles, orange_enemies, yellow_enemies, teal_enemies, pink_enemies, violet_enemies):
            group.clear()  # An empty field makes the next wave spawn right away
        globals()["active_boss"] = None
        console_message = f"Jumping to wave {number}"
    console_message_timer = 2.5

def purple_boss_break_orbs():
    """Console: break every orb on the Purple Boss at once (no purples spawn), so he can be shot. False if it can't."""
    global console_message, console_message_timer
    boss = active_boss
    if boss is None or boss["kind"] != "purple":
        console_message = "You're not fighting the Purple Boss"
        return False
    if not boss["orbs"]:
        console_message = "His orbs are already broken"
        return False
    for orb in boss["orbs"]:
        ox, oy = purple_boss_orb_position(boss, orb)
        for _ in range(4):
            spawn_death_effect(ox + random.uniform(-15, 15), oy + random.uniform(-15, 15), "purple")
    boss["orbs"] = []
    boss["shielded"] = boss["tethered"]
    boss["ripple"] = 0.4
    console_message, console_message_timer = "Purple Boss orbs broken", 2.5
    return True

def set_boss_health(kind, health):
    """Console: set the boss you're fighting to this health, as if you had shot it down to there
    (the Blue Boss shields up if that lands on 75, 50 or 25). Returns False if it can't."""
    global console_message, console_message_timer
    name = BOSSES[kind]["name"].title()
    boss = active_boss
    if boss is None or boss["kind"] != kind:
        console_message = f"You're not fighting the {name}"
        return False
    if not 1 <= health <= boss["max_health"]:
        console_message = f"Boss health must be 1 to {boss['max_health']}"
        return False
    boss["health"] = health
    boss["enraged"] = health <= BOSS_HEALTH // 2  # Red/Green call in their enemies from 50 down
    if kind == "teal":
        boss["events_done"] = [at for at in (175, 150, 125) if at > health]
        boss["shielded"] = False
        if boss["phase"] in ("swarm", "guard", "throw"):
            boss["phase"], boss["timer"] = "hidden", TEAL_BOSS_VANISH_WAIT
        if health < 150:
            # Below 150 he stays in the middle throwing teals
            boss["x"], boss["y"] = MAP_WIDTH / 2, MAP_HEIGHT / 2
            boss["phase"], boss["timer"] = "throw", 0.6
        if health == 175:
            teal_boss_start_guard(boss)
        elif health == 150:
            teal_boss_start_swarm(boss)
        elif health == 125:
            teal_boss_start_guard(boss, 125)
    if kind == "yellow":
        boss["events_done"] = [at for at in (75, 50, 25) if at > health]
        boss["event"], boss["shielded"], boss["arms"] = None, False, None
        boss["slot_offset"] = 0.0
        if health in (75, 50, 25):
            yellow_boss_event(boss, health)  # Landing right on 75, 50 or 25 starts that part of the fight
        elif health < 25:
            boss["event"] = "arms_warning"  # Straight to the warning, then the lines
            boss["arms_warning"] = {"angle": random.uniform(0, math.pi), "time": 0.0}
    if kind == "orange":
        boss["events_done"] = [at for at in (75, 50, 25) if at > health]
        if health in (75, 50, 25):
            orange_boss_start_lines(boss, health)  # Landing right on 75/50/25 starts those laser lines
        else:
            orange_boss_enter_stage(boss, orange_boss_stage_for(health))
    if kind == "purple":
        for orb in boss["orbs"]:
            spawn_death_effect(*purple_boss_orb_position(boss, orb), "purple")
        boss["orbs"] = []  # Skip straight past the orbs
        boss["tethered"] = False
        boss["events_done"] = [at for at in (75, 50, 25) if at > health]
        if health in (75, 50, 25):
            purple_boss_event(boss, health)  # Landing right on 75/50/25 starts that part of the fight
        boss["shielded"] = boss["tethered"]
    if kind == "blue":
        boss["shielded"] = False
        boss["shields_used"] = sum(1 for at in BLUE_BOSS_SHIELD_AT if at > health)
        boss["start"] = 0.0
        if boss["shields_used"] < len(BLUE_BOSS_SHIELD_AT) and health == BLUE_BOSS_SHIELD_AT[boss["shields_used"]]:
            boss["shields_used"] += 1  # Landing right on a shield point starts that shield
            boss["shielded"] = True
            boss["ripple"] = 0.4
            spawn_minions(BLUE_BOSS_SHIELD_MINIONS[boss["shields_used"] - 1])
    console_message, console_message_timer = f"{name} health set to {health}", 2.5
    return True

def go_to_boss_fight(number):
    """Boss commands: start a Waves game if you're not already in one, then jump to the boss's wave."""
    global start_screen, hub_open, settings_open, game_over
    in_waves_game = not (start_screen or hub_open or settings_open or game_over or in_shooting_range
                         or in_storm_survival or in_block_defence or in_tutorial)
    if not in_waves_game:
        exit_to_main_menu()  # Leaves any other mode properly first
        start_screen = hub_open = settings_open = game_over = False
        reset_game()
    jump_to_wave(number)

def run_console_command(text):
    """Handle whatever was typed into the console bar: "admin", a cheat code, or something unknown."""
    global console_open, console_input, console_message, console_message_timer, admin_code_open, admin_code_input
    global coin_cheat_enabled, kill_cheat_enabled, no_death_cheat_enabled
    command = text.strip().lower()
    if command == "admin":
        console_open = False
        console_input = ""
        admin_code_open = True
        admin_code_input = ""
        return
    compact = command.replace(" ", "")
    if compact.startswith("wave") and compact[4:].isdigit() and int(compact[4:]) >= 1:
        jump_to_wave(int(compact[4:]))
        close_console_stack()
        return
    boss_waves = {plan["boss"] + "boss": number for number, plan in WAVES.items() if plan.get("boss")}
    if compact in boss_waves:  # redboss, greenboss, blueboss: straight to that boss fight
        go_to_boss_fight(boss_waves[compact])
        close_console_stack()
        return
    if compact == "purplebossbreakorbs":  # Break all 4 of the Purple Boss's orbs at once
        if purple_boss_break_orbs():
            close_console_stack()
        else:
            console_input = ""
            console_message_timer = 3.0
        return
    for boss_command in boss_waves:  # redboss25, blueboss50...: set the current boss's health
        number = compact[len(boss_command):]
        if compact.startswith(boss_command) and number.isdigit():
            if set_boss_health(boss_command[:-len("boss")], int(number)):
                close_console_stack()
            else:
                console_input = ""
                console_message_timer = 3.0
            return
    cheat = CHEAT_CODES.get(command)
    if cheat == "coin":
        coin_cheat_enabled = True
        console_message = "Coin cheat on! Press L for +1000 coins"
    elif cheat == "kill":
        kill_cheat_enabled = True
        console_message = "Kill cheat on! Press K to kill all enemies"
    elif cheat == "no_death":
        no_death_cheat_enabled = True
        console_message = "No-death cheat on! Press M to toggle invincibility"
    else:
        console_message = "Unknown code"
    console_message_timer = 3.0
    console_input = ""
    if cheat:
        close_console_stack()

def admin_give_everything():
    """Unlock every skin, upgrade and ability, and top the coins up."""
    global shot_delay, main_game_coins, coin_count, console_message, console_message_timer
    g = globals()
    for skin in shop_skins:
        owned_skins[skin] = True
    for flag in UPGRADE_FLAGS:
        g[flag] = True
    shot_delay = GUN_SHOT_DELAYS[5]
    main_game_coins = coin_count = max(main_game_coins, 99999)
    g["sandbox_entry_coins"] = max(g["sandbox_entry_coins"], 99999)  # Still works from inside the Sandbox
    console_message, console_message_timer = "Admin: everything unlocked", 3.0

def admin_change_shop():
    """Reroll today's daily Shop for everyone on this PC (still resets at midnight)."""
    global console_message, console_message_timer
    cube_accounts.reroll_daily(save_data)
    console_message, console_message_timer = "Admin: daily Shop changed", 3.0

def draw_console_bar():
    """The typing bar that drops down from the top of the screen and stays there."""
    slide = ease_out_back(min(1.0, console_anim))
    bar = CONSOLE_BAR.move(0, -CONSOLE_BAR.height * (1 - slide))
    shadow = pygame.Surface((bar.width + 40, bar.height + 30), pygame.SRCALPHA)
    pygame.draw.rect(shadow, (0, 0, 0, 120), (20, 10, bar.width, bar.height), border_radius=18)
    screen.blit(shadow, (bar.x - 20, bar.y))
    # Brushed-metal panel with rounded bottom corners
    panel = pygame.Surface((bar.width, bar.height), pygame.SRCALPHA)
    for y in range(bar.height):
        t = y / (bar.height - 1)
        panel.fill((int(38 + 18 * (1 - t)), int(42 + 20 * (1 - t)), int(52 + 22 * (1 - t)), 245), (0, y, bar.width, 1))
    corner_mask = pygame.Surface((bar.width, bar.height), pygame.SRCALPHA)
    pygame.draw.rect(corner_mask, (255, 255, 255, 255), corner_mask.get_rect(),
                     border_bottom_left_radius=18, border_bottom_right_radius=18)
    panel.blit(corner_mask, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
    screen.blit(panel, bar.topleft)
    pygame.draw.rect(screen, (120, 200, 255), bar, 2, border_bottom_left_radius=18, border_bottom_right_radius=18)
    pygame.draw.line(screen, (120, 200, 255), (bar.x + 16, bar.bottom - 3), (bar.right - 16, bar.bottom - 3), 3)
    prompt = button_font.render(">", True, (120, 200, 255))
    screen.blit(prompt, prompt.get_rect(midleft=(bar.x + 22, bar.centery)))
    typed = button_font.render(console_input, True, WHITE)
    screen.blit(typed, typed.get_rect(midleft=(bar.x + 56, bar.centery)))
    if (pygame.time.get_ticks() // 400) % 2 == 0:  # Blinking cursor
        cursor_x = bar.x + 62 + typed.get_width()
        pygame.draw.line(screen, (120, 200, 255), (cursor_x, bar.centery - 16), (cursor_x, bar.centery + 16), 3)
    hint = smaller_button_font.render("Enter = run     Esc or ` = close", True, (150, 158, 170))
    screen.blit(hint, hint.get_rect(midright=(bar.right - 20, bar.centery)))

def draw_admin_code():
    """The "Enter code" box in the middle of the screen, after typing admin."""
    shade = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    shade.fill((0, 0, 0, 170))
    screen.blit(shade, (0, 0))
    panel = pygame.Rect(WIDTH // 2 - 260, HEIGHT // 2 - 120, 520, 240)
    draw_panel(panel)
    title = font.render("Enter code", True, WHITE)
    screen.blit(title, title.get_rect(center=(WIDTH // 2, panel.y + 50)))
    box = pygame.Rect(panel.x + 50, panel.y + 95, panel.width - 100, 64)
    pygame.draw.rect(screen, WHITE, box, border_radius=8)
    pygame.draw.rect(screen, (255, 200, 60), box, 3, border_radius=8)
    typed = font.render(admin_code_input, True, BLACK)
    typed_rect = typed.get_rect(center=box.center)
    screen.blit(typed, typed_rect)
    if (pygame.time.get_ticks() // 400) % 2 == 0:
        pygame.draw.line(screen, BLACK, (typed_rect.right + 6, box.y + 14), (typed_rect.right + 6, box.bottom - 14), 3)
    hint = small_button_font.render("Enter = confirm     Esc = cancel", True, (205, 210, 216))
    screen.blit(hint, hint.get_rect(center=(WIDTH // 2, panel.bottom - 34)))

def draw_admin_panel():
    shade = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    shade.fill((0, 0, 0, 180))
    screen.blit(shade, (0, 0))
    panel = pygame.Rect(WIDTH // 2 - 260, 250, 520, 420)
    draw_panel(panel)
    title = get_bubble_text("ADMIN", 64, (255, 215, 130), (255, 120, 40))
    screen.blit(title, title.get_rect(center=(WIDTH // 2, panel.y + 62)))
    subtitle = small_button_font.render("These change things for real", True, (205, 210, 216))
    screen.blit(subtitle, subtitle.get_rect(center=(WIDTH // 2, panel.y + 128)))
    for rect, label, color in ((ADMIN_GIVE_BUTTON, "Give Everything", BLUE),
                               (ADMIN_SHOP_BUTTON, "Change Shop", BLUE),
                               (ADMIN_CLOSE_BUTTON, "Close", RED)):
        draw_button(rect, color)
        text = button_font.render(label, True, BLACK)
        screen.blit(text, text.get_rect(center=rect.center))

# ---- Pause menu (Escape during a game) ----
pause_menu_open = False
pause_menu_anim = 0.0        # 0 = hidden above the screen, 1 = fully down
settings_from_pause = False  # So Back in Settings knows where to return to
PAUSE_MENU_BUTTONS = ["Resume", "Settings", "Main Menu", "Quit"]

def exit_to_main_menu():
    """Leave the current game and go back to the main menu (same as the in-game Exit button)."""
    global start_screen, in_shooting_range, in_storm_survival, in_block_defence, block_defence_coins
    global coin_count, current_skin, owned_skins, equipped_ability, shot_delay, in_tutorial
    global game_over, game_paused, pause_countdown
    g = globals()
    g["enemy_menu_open"] = False  # Leaving the Sandbox closes its menu
    g["block_menu_open"] = False
    start_screen = True
    game_over = False
    game_paused = False
    pause_countdown = 0.0
    if in_tutorial:
        in_tutorial = False
        coin_count = main_game_coins  # Tutorial coins were practice only
    if in_shooting_range:
        # Everything is free in the Shooting Range, so put the real progress back
        in_shooting_range = False
        coin_count = main_game_coins
        current_skin = main_game_skin
        owned_skins = main_game_owned_skins.copy()
        for flag in UPGRADE_FLAGS:
            g[flag] = g["main_game_" + flag]
        equipped_ability = main_game_equipped_ability
        shot_delay = main_game_shot_delay
    elif in_storm_survival:
        in_storm_survival = False
    elif in_block_defence:
        in_block_defence = False
        block_defence_coins = 0  # Block Defence coins don't carry over

def pause_menu_rects():
    """Panel and buttons at the menu's current slide position."""
    panel_height = 420
    resting_y = HEIGHT // 2 - panel_height // 2  # Middle of the screen
    y = -panel_height + (panel_height + resting_y) * ease_out_back(min(1.0, pause_menu_anim))
    panel = pygame.Rect(WIDTH // 2 - 230, y, 460, panel_height)
    buttons = [(name, pygame.Rect(panel.x + 80, panel.y + 120 + i * 70, 300, 58))
               for i, name in enumerate(PAUSE_MENU_BUTTONS)]
    return panel, buttons

def open_pause_menu():
    global pause_menu_open, game_paused, pause_countdown
    pause_menu_open = True
    game_paused = True
    pause_countdown = 0.0

def close_pause_menu(resume=True):
    """Close the menu. Resuming gives the usual 3-2-1 countdown before play carries on."""
    global pause_menu_open, pause_countdown
    pause_menu_open = False
    if resume:
        pause_countdown = pause_countdown_duration

def draw_pause_menu():
    shade = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    shade.fill((0, 0, 0, int(150 * min(1.0, pause_menu_anim))))
    screen.blit(shade, (0, 0))
    panel, buttons = pause_menu_rects()
    draw_panel(panel)
    title = get_bubble_text("Pause Menu", 54, (255, 240, 150), (255, 160, 40))
    screen.blit(title, title.get_rect(center=(panel.centerx, panel.y + 60)))
    for name, rect in buttons:
        draw_button(rect, RED if name == "Quit" else BLUE)
        text = button_font.render(name, True, BLACK)
        screen.blit(text, text.get_rect(center=rect.center))

def handle_pause_menu_event(event):
    global pause_menu_open, pause_menu_anim, settings_open, settings_confirm, settings_from_pause
    if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
        close_pause_menu()
        return
    if event.type != pygame.MOUSEBUTTONDOWN or event.button != 1 or pause_menu_anim < 0.9:
        return  # Ignore clicks until the menu has finished sliding down
    pos = pygame.mouse.get_pos()
    for name, rect in pause_menu_rects()[1]:
        if not rect.collidepoint(pos):
            continue
        if name == "Resume":
            close_pause_menu()
        elif name == "Settings":
            pause_menu_open = False
            pause_menu_anim = 0.0  # Gone at once, rather than sliding away over the Settings screen
            settings_open = True
            settings_confirm = None
            settings_from_pause = True
        elif name == "Main Menu":
            pause_menu_open = False
            pause_menu_anim = 0.0
            exit_to_main_menu()
        elif name == "Quit":
            pygame.quit()
            sys.exit()
        return

# ---- Orange laser enemy (Sandbox only for now) ----
orange_enemies = []  # Each is a dict: position, which way its gun points, and its laser
ORANGE_SPEED = 1.1                    # Walks a little slower than a red enemy
ORANGE_ATTACK_RANGE = 420             # Plants itself and fires once the player is this close
ORANGE_LEASH_RANGE = 650              # Pulls its laser back in once the player gets this far away
ORANGE_WINDUP = 0.6                   # Seconds of glowing at the gun before the laser comes out
ORANGE_EXTEND_SPEED = 750             # How fast the laser grows (pixels per second)
ORANGE_TURN_SPEED = math.radians(30)  # How fast the laser swings after the player (per second) - slow on purpose
ORANGE_BEAM_WIDTH = 10
ORANGE_GUN_LENGTH = 55                # A bigger gun than the player's or the blue enemy's

def new_orange_enemy(x, y):
    return {"x": x, "y": y, "angle": 0.0, "firing": False, "windup": 0.0, "beam": 0.0, "drawn": 0.0}

def turn_toward(current, target, max_step):
    """Turn an angle toward a target angle by at most max_step."""
    diff = (target - current + math.pi) % (2 * math.pi) - math.pi
    return target if abs(diff) <= max_step else current + math.copysign(max_step, diff)

def laser_reach(x, y, angle):
    """How far a laser from (x, y) travels along `angle` before it hits the barrier."""
    if in_storm_survival:
        left = MAP_WIDTH // 2 - storm_survival_map_width // 2
        top = MAP_HEIGHT // 2 - storm_survival_map_height // 2
        right, bottom = left + storm_survival_map_width, top + storm_survival_map_height
    else:
        left, top, right, bottom = 0, 0, MAP_WIDTH, MAP_HEIGHT
    dx, dy = math.cos(angle), math.sin(angle)
    reach = []
    if dx > 1e-9:
        reach.append((right - x) / dx)
    elif dx < -1e-9:
        reach.append((left - x) / dx)
    if dy > 1e-9:
        reach.append((bottom - y) / dy)
    elif dy < -1e-9:
        reach.append((top - y) / dy)
    return max(0.0, min(reach)) if reach else 0.0

def shield_stops_laser(start_x, start_y, angle, length):
    """If the player's shield is up and in the laser's path, how far along the laser it gets stopped (else None)."""
    if not (has_shield and equipped_ability == 'shield' and shield_active):
        return None
    px, py = player_x + player_size / 2, player_y + player_size / 2
    dx, dy = math.cos(angle), math.sin(angle)
    fx, fy = start_x - px, start_y - py
    b = fx * dx + fy * dy
    c = fx * fx + fy * fy - SHIELD_RADIUS ** 2
    if c < 0 or b * b - c < 0:
        return None  # Starts inside the shield's circle, or never reaches it
    t = -b - math.sqrt(b * b - c)  # Where the laser first reaches the shield's circle
    if not 0 <= t <= length:
        return None
    hit_angle = math.atan2(start_y + dy * t - py, start_x + dx * t - px)
    off_centre = (hit_angle - last_rot_angle + math.pi) % (2 * math.pi) - math.pi
    return t if abs(off_centre) <= SHIELD_ARC / 2 else None

def point_to_segment_distance(px, py, ax, ay, bx, by):
    abx, aby = bx - ax, by - ay
    length_sq = abx * abx + aby * aby
    t = 0.0 if length_sq == 0 else max(0.0, min(1.0, ((px - ax) * abx + (py - ay) * aby) / length_sq))
    return math.hypot(px - (ax + abx * t), py - (ay + aby * t))

def player_hit():
    """The player has been hit: game over, with the same clean-up as touching an enemy."""
    global game_over, block_defence_coins, shield_cooldown, teleport_cooldown, freeze_cooldown, freeze_active, freeze_timer
    game_over = True
    if in_block_defence:
        block_defence_coins = 0
    shield_cooldown = teleport_cooldown = freeze_cooldown = 0.0
    freeze_active = False
    freeze_timer = 0.0

def update_orange_enemies(dt):
    """Walk toward the player; once close, plant, wind up, and fire one long laser that grows until it hits
    the barrier and slowly swings after the player. It pulls the laser back in if the player gets far away."""
    frozen = has_freeze and equipped_ability == 'freeze' and freeze_active
    half = player_size / 2
    lpx, lpy = player_x + half, player_y + half  # You (for getting hit)
    attack_range = BLOCK_ORANGE_RANGE if in_block_defence else ORANGE_ATTACK_RANGE
    for enemy in orange_enemies:
        if frozen:
            continue  # Frozen solid: no walking, turning or firing (and the laser can't hurt you)
        target_x, target_y = enemy_target(enemy["x"], enemy["y"])
        px, py = target_x + half, target_y + half
        cx, cy = enemy["x"] + half, enemy["y"] + half
        distance = math.hypot(px - cx, py - cy)
        to_player = math.atan2(py - cy, px - cx)
        if not enemy["firing"]:
            enemy["angle"] = turn_toward(enemy["angle"], to_player, math.radians(240) * dt)
            enemy["beam"] = max(0.0, enemy["beam"] - ORANGE_EXTEND_SPEED * 2 * dt)  # Pull any laser back in
            if distance > 1:
                enemy["x"] += (px - cx) / distance * ORANGE_SPEED
                enemy["y"] += (py - cy) / distance * ORANGE_SPEED
            if distance <= attack_range:
                enemy["firing"] = True
                enemy["windup"] = 0.0
        elif distance > ORANGE_LEASH_RANGE and not in_block_defence:
            enemy["firing"] = False  # Player got away
        else:
            enemy["angle"] = turn_toward(enemy["angle"], to_player, ORANGE_TURN_SPEED * dt)
            enemy["windup"] += dt
            if enemy["windup"] >= ORANGE_WINDUP:
                enemy["beam"] += ORANGE_EXTEND_SPEED * dt
        # The laser stops at the barrier, or at the shield if it is in the way
        start_x = cx + math.cos(enemy["angle"]) * ORANGE_GUN_LENGTH
        start_y = cy + math.sin(enemy["angle"]) * ORANGE_GUN_LENGTH
        enemy["beam"] = min(enemy["beam"], laser_reach(start_x, start_y, enemy["angle"]))
        if in_block_defence:
            to_block = ray_to_rect(start_x, start_y, enemy["angle"], BLOCK_DEFENCE_BLOCK_RECT)
            if to_block is not None and enemy["beam"] >= to_block:
                enemy["beam"] = to_block  # The laser stops on the block and burns it
                if enemy["firing"] and not frozen:
                    enemy["burn"] = enemy.get("burn", 0.0) + dt
                    while enemy["burn"] >= BLOCK_ORANGE_TICK and block_health > 0:
                        enemy["burn"] -= BLOCK_ORANGE_TICK
                        damage_block(1)
        stopped = shield_stops_laser(start_x, start_y, enemy["angle"], enemy["beam"])
        enemy["drawn"] = enemy["beam"] if stopped is None else stopped
        if game_over or player_safe():
            continue
        if math.hypot(lpx - cx, lpy - cy) < player_size:  # Touching the enemy itself
            player_hit()
        elif enemy["firing"] and enemy["beam"] > 0 and stopped is None:
            end_x = start_x + math.cos(enemy["angle"]) * enemy["beam"]
            end_y = start_y + math.sin(enemy["angle"]) * enemy["beam"]
            if point_to_segment_distance(lpx, lpy, start_x, start_y, end_x, end_y) < half + ORANGE_BEAM_WIDTH / 2:
                player_hit()

def draw_orange_enemies():
    """Orange enemies with their big guns, their charge-up glow, and their lasers."""
    half = player_size / 2
    look_x, look_y = enemy_target()[0] - camera_x + half, enemy_target()[1] - camera_y + half
    t = pygame.time.get_ticks() / 1000
    lit = [e for e in orange_enemies if e["drawn"] > 0 or (e["firing"] and e["windup"] < ORANGE_WINDUP)]
    if lit:
        # The glow layer only needs to cover the lasers (clipped to the screen), not the whole window
        area = None
        for enemy in lit:
            dx, dy = math.cos(enemy["angle"]), math.sin(enemy["angle"])
            sx = enemy["x"] - camera_x + half + dx * ORANGE_GUN_LENGTH
            sy = enemy["y"] - camera_y + half + dy * ORANGE_GUN_LENGTH
            ex, ey = sx + dx * enemy["drawn"], sy + dy * enemy["drawn"]
            clipped = screen.get_rect().inflate(60, 60).clipline((sx, sy), (ex, ey))
            if clipped:
                (x1, y1), (x2, y2) = clipped
                box = pygame.Rect(min(x1, x2), min(y1, y2), abs(x2 - x1) + 1, abs(y2 - y1) + 1).inflate(60, 60)
                area = box if area is None else area.union(box)
        area = area.clip(screen.get_rect()) if area is not None else pygame.Rect(0, 0, 0, 0)
    if lit and area.width > 0 and area.height > 0:
        layer = pygame.Surface(area.size, pygame.SRCALPHA)
        ox, oy = area.topleft
        for enemy in lit:
            dx, dy = math.cos(enemy["angle"]), math.sin(enemy["angle"])
            sx = enemy["x"] - camera_x + half + dx * ORANGE_GUN_LENGTH - ox
            sy = enemy["y"] - camera_y + half + dy * ORANGE_GUN_LENGTH - oy
            if enemy["firing"] and enemy["windup"] < ORANGE_WINDUP:
                charge = enemy["windup"] / ORANGE_WINDUP  # Charging up: a growing glow at the gun
                pygame.draw.circle(layer, (255, 60, 50, int(90 + 120 * charge)), (sx, sy), 6 + 14 * charge)
                pygame.draw.circle(layer, (255, 225, 220, int(160 + 90 * charge)), (sx, sy), 3 + 6 * charge)
            if enemy["drawn"] > 0:
                ex, ey = sx + dx * enemy["drawn"], sy + dy * enemy["drawn"]
                live = enemy["firing"]  # A laser being pulled back in is fainter (and harmless)
                flicker = 0.85 + 0.15 * math.sin(t * 40 + enemy["x"])
                pygame.draw.line(layer, (255, 20, 20, int((110 if live else 45) * flicker)), (sx, sy), (ex, ey), 26)
                pygame.draw.line(layer, (255, 50, 40, int((230 if live else 90) * flicker)), (sx, sy), (ex, ey), 12)
                pygame.draw.line(layer, (255, 170, 160, 255 if live else 110), (sx, sy), (ex, ey), 4)
                pygame.draw.circle(layer, (255, 120, 110, 200 if live else 80), (ex, ey), 12 * flicker)  # Where it hits
        screen.blit(layer, area.topleft)
    for enemy in orange_enemies:
        cx, cy = enemy["x"] - camera_x + half, enemy["y"] - camera_y + half
        if not on_screen(cx, cy, 100):
            continue
        dx, dy = math.cos(enemy["angle"]), math.sin(enemy["angle"])
        draw_shadow(enemy_shadow, cx, cy)
        barrel_end = (cx + dx * ORANGE_GUN_LENGTH, cy + dy * ORANGE_GUN_LENGTH)
        pygame.draw.line(screen, (35, 30, 28), (cx, cy), barrel_end, 20)
        pygame.draw.line(screen, (125, 115, 105), (cx, cy), barrel_end, 8)
        pygame.draw.circle(screen, (35, 30, 28), barrel_end, 11)
        pygame.draw.circle(screen, (255, 80, 70), barrel_end, 5)
        draw_orb(orange_orb, None, cx, cy)
        draw_eye(cx, cy, look_x, look_y, 8, half * 0.45)

# ---- Yellow orb-flinging enemy ----
yellow_enemies = []  # Each is a dict: position, its spinning orb, and what the orb is doing (spinning, charging, regrowing)
YELLOW_SPEED = 1.3
YELLOW_ORB_DISTANCE = 48          # How far the orb circles from the yellow's center
YELLOW_ORB_RADIUS = 10
YELLOW_ORB_SPIN = math.radians(720)  # Fast: two laps per second
YELLOW_FLING_RANGE = 380          # Starts charging when the player is this close
YELLOW_CHARGE_TIME = 1.0          # The orb swings round, glows and turns red for this long before it's flung
YELLOW_FLING_SPEED = 9            # Pixels per frame
YELLOW_CURVE = math.radians(0.7)  # How much the flung orb can bend toward the player each frame (a little)
YELLOW_CURVE_TIME = 1.1           # It only curves for this long, so it can't circle around forever
YELLOW_REGROW_TIME = 1.8          # A new orb grows back before it can fling again

def new_yellow_enemy(x, y):
    return {"x": x, "y": y, "orb_angle": random.uniform(0, 2 * math.pi), "state": "spin", "timer": 0.0}

def yellow_orb_position(enemy):
    half = player_size / 2
    return (enemy["x"] + half + math.cos(enemy["orb_angle"]) * YELLOW_ORB_DISTANCE,
            enemy["y"] + half + math.sin(enemy["orb_angle"]) * YELLOW_ORB_DISTANCE)

storm_spawn_seconds = {}  # Barrier Shrink: the last whole second each kind of enemy spawned

def storm_spawn_due(kind, interval):
    if net_role() == "guest":
        return False  # The host spawns; this game shows what the host sends
    """True once per matching second: every `interval` seconds of the Barrier Shrink timer."""
    second = int(game_timer)
    if second > 0 and second % interval == 0 and storm_spawn_seconds.get(kind) != second:
        storm_spawn_seconds[kind] = second
        return True
    return False

def dict_enemy_groups():
    """The enemies stored as dicts, with their kind name."""
    return (("orange", orange_enemies), ("yellow", yellow_enemies), ("teal", teal_enemies), ("pink", pink_enemies), ("violet", violet_enemies))

# ---- Violet pulling enemy ----
violet_enemies = []  # Each is a dict: position and a spin angle for its swirl
VIOLET_PULL_RANGE = 420      # Starts pulling the player in inside this distance
VIOLET_MAX_PULL = 8.5        # Pull (pixels per frame) right next to it - faster than the player can walk (5)
VIOLET_MIN_PULL = 0.6        # Pull at the very edge of its range

def new_violet_enemy(x, y):
    return {"x": x, "y": y, "swirl": random.uniform(0, 2 * math.pi)}

def violet_pull_strength(distance):
    """0 outside the range; grows faster and faster as the player gets closer."""
    if distance >= VIOLET_PULL_RANGE:
        return 0.0
    closeness = 1 - distance / VIOLET_PULL_RANGE  # 0 at the edge, 1 right next to it
    return VIOLET_MIN_PULL + (VIOLET_MAX_PULL - VIOLET_MIN_PULL) * closeness ** 1.3  # Within ~150px you can't walk away

def update_violet_enemies(dt):
    """Violets never move. Any in range drag the player toward them; touching one kills."""
    global player_x, player_y
    if has_freeze and equipped_ability == 'freeze' and freeze_active:
        return
    half = player_size / 2
    for enemy in violet_enemies:
        enemy["swirl"] = (enemy["swirl"] + dt * 3) % (2 * math.pi)
    if in_block_defence or game_over:
        return
    for enemy in violet_enemies:
        cx, cy = enemy["x"] + half, enemy["y"] + half
        px, py = player_x + half, player_y + half
        distance = math.hypot(cx - px, cy - py)
        pull = violet_pull_strength(distance)
        if pull > 0 and distance > 1:
            step = min(pull, distance)
            player_x += (cx - px) / distance * step
            player_y += (cy - py) / distance * step
        if not player_safe() and math.hypot(enemy["x"] - player_x, enemy["y"] - player_y) < player_size:
            player_hit()
            return

def violet_hit(bullet_rect):
    global kills
    for enemy in violet_enemies:
        if bullet_rect.colliderect(pygame.Rect(enemy["x"], enemy["y"], player_size, player_size)):
            violet_enemies.remove(enemy)
            enemy_killed(enemy["x"], enemy["y"], "violet")
            kills += 1
            return True
    return False

def draw_violet_enemies():
    half = player_size / 2
    look_x, look_y = player_x - camera_x + half, player_y - camera_y + half
    px, py = player_x + half, player_y + half
    for enemy in violet_enemies:
        cx, cy = enemy["x"] - camera_x + half, enemy["y"] - camera_y + half
        if not on_screen(cx, cy, VIOLET_PULL_RANGE):
            continue
        distance = math.hypot(enemy["x"] + half - px, enemy["y"] + half - py)
        strength = violet_pull_strength(distance) / VIOLET_MAX_PULL  # 0..1, how hard it's pulling right now
        near = distance < VIOLET_PULL_RANGE + 250  # Only draw the big pull area when the player is close to it
        reach = VIOLET_PULL_RANGE if near else half + 110
        size = int(reach * 2 + 20)
        swirl = pygame.Surface((size, size), pygame.SRCALPHA)
        c = size / 2
        t = pygame.time.get_ticks() / 1000
        if near:
            pygame.draw.circle(swirl, (170, 130, 255, int(30 + 50 * strength)), (c, c), VIOLET_PULL_RANGE)  # Pull area
            pygame.draw.circle(swirl, (190, 140, 255, int(130 + 100 * strength)), (c, c), VIOLET_PULL_RANGE, 3)
            for k in range(3):  # Rings shrinking inward, faster when it's pulling hard
                r = VIOLET_PULL_RANGE * (1 - ((t * (0.35 + 0.9 * strength) + k / 3) % 1))
                pygame.draw.circle(swirl, (185, 135, 255, int(110 + 130 * strength)), (c, c), max(4, r), 3)
        for k in range(6):  # Spiral arms
            a = enemy["swirl"] + k * math.pi / 3
            pts = [(c + math.cos(a + j * 0.35) * (half + 12 + j * 16), c + math.sin(a + j * 0.35) * (half + 12 + j * 16)) for j in range(6)]
            pygame.draw.lines(swirl, (195, 145, 255, int(170 + 85 * strength)), False, pts, 4)
        screen.blit(swirl, (cx - c, cy - c))
        draw_orb(violet_orb, enemy_shadow, cx, cy)
        draw_eye(cx, cy, look_x, look_y, 8, half * 0.3)

# ---- Pink diagonal dashing enemy ----
pink_enemies = []  # Each is a dict: position, which diagonal it's dashing along, and its dash / pause state
PINK_DASH_LENGTH = 150       # How far each diagonal dash goes
PINK_DASH_SPEED = 1100       # Pixels per second while dashing (fast, like the Green Boss's dash)
PINK_PAUSE = 0.3             # Short stop between dashes

def new_pink_enemy(x, y):
    return {"x": x, "y": y, "dir": (1, 1), "state": "pause", "timer": random.uniform(0, PINK_PAUSE), "left": 0.0, "trail": []}

def pink_pick_diagonal(enemy, target_x, target_y):
    """The diagonal toward the player; if it's lined up on one axis, switch sides on that axis (zigzag)."""
    dx = target_x - enemy["x"]
    dy = target_y - enemy["y"]
    sx = -enemy["dir"][0] if abs(dx) < PINK_DASH_LENGTH / 3 else (1 if dx > 0 else -1)
    sy = -enemy["dir"][1] if abs(dy) < PINK_DASH_LENGTH / 3 else (1 if dy > 0 else -1)
    return sx, sy

def update_pink_enemies(dt):
    """Pinks dash along diagonals only, like the Green Boss's dash: a quick diagonal dash, a 0.3 s stop, then the next dash - zigzagging toward the player."""
    if has_freeze and equipped_ability == 'freeze' and freeze_active:
        return
    for enemy in pink_enemies:
        enemy["trail"] = [(x, y, age + dt) for x, y, age in enemy["trail"] if age + dt < 0.2]
        if enemy["state"] == "pause":
            if enemy["timer"] == 0.0 or "next" not in enemy:
                enemy["next"] = pink_pick_diagonal(enemy, *enemy_target(enemy["x"], enemy["y"]))
            enemy["timer"] += dt
            if enemy["timer"] >= PINK_PAUSE:
                enemy["dir"] = enemy.pop("next")
                enemy["state"], enemy["left"] = "dash", PINK_DASH_LENGTH
        else:
            step = min(enemy["left"], PINK_DASH_SPEED * dt)
            sx, sy = enemy["dir"]
            enemy["trail"].append((enemy["x"], enemy["y"], 0.0))
            enemy["x"] += sx * step / math.sqrt(2)
            enemy["y"] += sy * step / math.sqrt(2)
            enemy["left"] -= step
            if enemy["left"] <= 0.01:
                enemy["state"], enemy["timer"] = "pause", 0.0
    if not game_over and not player_safe():
        for enemy in pink_enemies:
            if math.hypot(enemy["x"] - player_x, enemy["y"] - player_y) < player_size:
                player_hit()
                break

def pink_hit(bullet_rect):
    global kills
    for enemy in pink_enemies:
        if bullet_rect.colliderect(pygame.Rect(enemy["x"], enemy["y"], player_size, player_size)):
            pink_enemies.remove(enemy)
            enemy_killed(enemy["x"], enemy["y"], "pink")
            kills += 1
            return True
    return False

def draw_pink_enemies():
    half = player_size / 2
    look_x, look_y = player_x - camera_x + half, player_y - camera_y + half
    for enemy in pink_enemies:
        cx, cy = enemy["x"] - camera_x + half, enemy["y"] - camera_y + half
        if not on_screen(cx, cy, PINK_DASH_LENGTH + 40):
            continue
        for x, y, age in enemy["trail"]:  # Afterimages while dashing
            fade = 1 - age / 0.2
            ghost = pygame.Surface((player_size, player_size), pygame.SRCALPHA)
            pygame.draw.circle(ghost, (255, 120, 190, int(110 * fade)), (half, half), half * (0.6 + 0.4 * fade))
            screen.blit(ghost, (x - camera_x, y - camera_y))
        draw_orb(pink_orb, enemy_shadow, cx, cy)
        draw_eye(cx, cy, look_x, look_y, 8, half * 0.3)

# ---- Teal exploding enemy ----
teal_enemies = []  # Each is a dict: position, and its fuse (None while hunting, seconds lit once it's close)
TEAL_SPEED = 3.8                 # Faster than a green (3.0)
TEAL_TRIGGER_RANGE = 120         # Stops and lights its fuse this close to the player
TEAL_FUSE = 2.0                  # Seconds of flashing before it explodes
TEAL_BLAST_RADIUS = 140          # The explosion kills the player inside this distance
TEAL_HIDDEN_ALPHA = 45           # Almost fully see-through while hunting

def new_teal_enemy(x, y):
    return {"x": x, "y": y, "fuse": None, "blink_phase": 0.0}

def update_teal_enemies(dt):
    """Hunt the player nearly invisible; once close, stop, flash faster and faster for 2 seconds, then explode."""
    if has_freeze and equipped_ability == 'freeze' and freeze_active:
        return
    half = player_size / 2
    for enemy in teal_enemies[:]:
        target_x, target_y = enemy_target(enemy["x"], enemy["y"])
        px, py = target_x + half, target_y + half
        cx, cy = enemy["x"] + half, enemy["y"] + half
        distance = math.hypot(px - cx, py - cy)
        if enemy["fuse"] is None:
            if distance <= TEAL_TRIGGER_RANGE:
                enemy["fuse"] = 0.0
            elif distance > 1:
                enemy["x"] += (px - cx) / distance * TEAL_SPEED
                enemy["y"] += (py - cy) / distance * TEAL_SPEED
            continue
        if enemy.get("thrown_to"):
            tx, ty = enemy["thrown_to"]
            gap = math.hypot(tx - enemy["x"], ty - enemy["y"])
            step = TEAL_THROWN_SPEED * dt
            if gap <= step:
                enemy["x"], enemy["y"] = tx, ty
                enemy["thrown_to"] = None  # Landed
            else:
                enemy["x"] += (tx - enemy["x"]) / gap * step
                enemy["y"] += (ty - enemy["y"]) / gap * step
        fuse_len = enemy.get("fuse_len", TEAL_FUSE)
        enemy["fuse"] += dt
        # Blinks from 3 flashes a second up to 16 as the fuse burns down
        enemy["blink_phase"] += (3 + 13 * min(1.0, enemy["fuse"] / fuse_len)) * dt
        if enemy["fuse"] >= fuse_len:
            teal_explode(enemy)

def teal_explode(enemy):
    half = player_size / 2
    cx, cy = enemy["x"] + half, enemy["y"] + half
    if enemy in teal_enemies:
        teal_enemies.remove(enemy)
    sounds.play("teal_explode")
    effects.append({"type": "flash", "x": cx, "y": cy, "age": 0.0, "life": 0.45, "color": (60, 255, 230), "size": 3.2})
    for _ in range(1 if enemy.get("swarm") else 3):  # Swarms of 100 use a lighter burst so the game doesn't lag
        spawn_death_effect(cx + random.uniform(-20, 20), cy + random.uniform(-20, 20), "teal")
    px, py = player_x + half, player_y + half
    if not game_over and not player_safe() and math.hypot(px - cx, py - cy) < TEAL_BLAST_RADIUS + half:
        player_hit()

def teal_hit(bullet_rect):
    """A player shot hitting a teal kills it (it doesn't explode)."""
    global kills
    for enemy in teal_enemies:
        if bullet_rect.colliderect(pygame.Rect(enemy["x"], enemy["y"], player_size, player_size)):
            teal_enemies.remove(enemy)
            enemy_killed(enemy["x"], enemy["y"], "teal")
            kills += 1
            return True
    return False

def draw_teal_enemies():
    half = player_size / 2
    look_x, look_y = player_x - camera_x + half, player_y - camera_y + half
    for enemy in teal_enemies:
        cx, cy = enemy["x"] - camera_x + half, enemy["y"] - camera_y + half
        if not on_screen(cx, cy, 160):
            continue
        if enemy["fuse"] is None:
            alpha = TEAL_HIDDEN_ALPHA
        else:
            alpha = 255 if math.sin(enemy["blink_phase"] * 2 * math.pi) > 0 else 20  # Flashing visible / invisible
            charge = min(1.0, enemy["fuse"] / enemy.get("fuse_len", TEAL_FUSE))
            ring = pygame.Surface((TEAL_BLAST_RADIUS * 2 + 20, TEAL_BLAST_RADIUS * 2 + 20), pygame.SRCALPHA)
            c = TEAL_BLAST_RADIUS + 10
            pygame.draw.circle(ring, (60, 255, 230, int(30 + 50 * charge)), (c, c), TEAL_BLAST_RADIUS)  # Blast area
            pygame.draw.circle(ring, (180, 255, 245, int(90 + 140 * charge)), (c, c), TEAL_BLAST_RADIUS, 3)
            pygame.draw.circle(ring, (180, 255, 245, 160), (c, c), max(4, TEAL_BLAST_RADIUS * (1 - charge)), 2)  # Closing in
            screen.blit(ring, (cx - c, cy - c))
        teal_orb.set_alpha(alpha)
        enemy_shadow.set_alpha(int(alpha * 0.6))
        draw_orb(teal_orb, enemy_shadow, cx, cy)
        # Back to fully opaque. (Never set_alpha(None) on these: it removes their transparency and they draw as black boxes.)
        enemy_shadow.set_alpha(255)
        teal_orb.set_alpha(255)
        if alpha > 120:
            draw_eye(cx, cy, look_x, look_y, 8, half * 0.3)



def update_yellow_enemies(dt):
    """Walk toward the player spinning the orb. Close up, the orb swings round to face the player, charges for a
    second (turning red) and gets flung as a shot that curves a little toward the player. Then it grows back."""
    if has_freeze and equipped_ability == 'freeze' and freeze_active:
        return
    half = player_size / 2
    for enemy in yellow_enemies:
        target_x, target_y = nearest_player(enemy["x"], enemy["y"])
        px, py = target_x + half, target_y + half
        cx, cy = enemy["x"] + half, enemy["y"] + half
        distance = math.hypot(px - cx, py - cy)
        if distance > 1:
            enemy["x"] += (px - cx) / distance * YELLOW_SPEED
            enemy["y"] += (py - cy) / distance * YELLOW_SPEED
        to_player = math.atan2(py - cy, px - cx)
        if enemy["state"] == "spin":
            enemy["orb_angle"] = (enemy["orb_angle"] + YELLOW_ORB_SPIN * dt) % (2 * math.pi)
            if distance <= YELLOW_FLING_RANGE:
                enemy["state"], enemy["timer"] = "charge", 0.0
        elif enemy["state"] == "charge":
            enemy["orb_angle"] = turn_toward(enemy["orb_angle"], to_player, math.radians(720) * dt)
            enemy["timer"] += dt
            if enemy["timer"] >= YELLOW_CHARGE_TIME:
                ox, oy = yellow_orb_position(enemy)
                aim = math.hypot(px - ox, py - oy) or 1
                size = bullet_size * 3
                blue_bullets.append({"x": ox - size / 2, "y": oy - size / 2, "scale": 3, "orb": True, "curve_time": YELLOW_CURVE_TIME,
                                     "dx": (px - ox) / aim * YELLOW_FLING_SPEED, "dy": (py - oy) / aim * YELLOW_FLING_SPEED})
                enemy["state"], enemy["timer"] = "regrow", 0.0
        elif enemy["state"] == "regrow":
            enemy["orb_angle"] = (enemy["orb_angle"] + YELLOW_ORB_SPIN * dt) % (2 * math.pi)
            enemy["timer"] += dt
            if enemy["timer"] >= YELLOW_REGROW_TIME:
                enemy["state"], enemy["timer"] = "spin", 0.0

def curve_flung_orb(shot, dt):
    """A flung yellow orb bends a little toward the player for a short time."""
    if shot.get("curve_time", 0) <= 0:
        return
    shot["curve_time"] -= dt
    size = shot_size(shot)
    heading = math.atan2(shot["dy"], shot["dx"])
    aim_x, aim_y = nearest_player(shot["x"], shot["y"])
    target = math.atan2(aim_y + player_size / 2 - (shot["y"] + size / 2), aim_x + player_size / 2 - (shot["x"] + size / 2))
    heading = turn_toward(heading, target, YELLOW_CURVE)
    speed = math.hypot(shot["dx"], shot["dy"])
    shot["dx"], shot["dy"] = math.cos(heading) * speed, math.sin(heading) * speed

def yellow_catches(bullet_rect):
    """A player bullet hitting a yellow's body kills it. (Its orb no longer catches shots.)"""
    global kills
    for enemy in yellow_enemies:
        if bullet_rect.colliderect(pygame.Rect(enemy["x"], enemy["y"], player_size, player_size)):
            yellow_enemies.remove(enemy)
            enemy_killed(enemy["x"], enemy["y"], "yellow")
            kills += 1
            return True
    return False

def draw_flung_orb(x, y, t, radius=12, color="red"):
    """A flung orb: a hot red ball (yellow enemies) or a big yellow energy ball (Yellow Boss), with a glow."""
    core, mid, outer = ((255, 70, 50), (255, 120, 60), (255, 60, 40)) if color == "red" else ((255, 215, 40), (255, 235, 120), (255, 180, 30))
    size = int(radius * 3 + 20)
    glow = pygame.Surface((size, size), pygame.SRCALPHA)
    c = size / 2
    pulse = 0.8 + 0.2 * math.sin(t * 30)
    pygame.draw.circle(glow, (*outer, 90), (c, c), radius * 1.8 * pulse)
    pygame.draw.circle(glow, (*mid, 170), (c, c), radius * 1.25)
    screen.blit(glow, (x - c, y - c))
    pygame.draw.circle(screen, core, (x, y), radius)
    pygame.draw.circle(screen, (255, 250, 220), (x, y), max(2, radius // 2))

def draw_yellow_enemies():
    half = player_size / 2
    look_x, look_y = player_x - camera_x + half, player_y - camera_y + half
    t = pygame.time.get_ticks() / 1000
    for enemy in yellow_enemies:
        cx, cy = enemy["x"] - camera_x + half, enemy["y"] - camera_y + half
        if not on_screen(cx, cy, 120):
            continue
        draw_shadow(enemy_shadow, cx, cy)
        draw_orb(yellow_orb, None, cx, cy)
        draw_eye(cx, cy, look_x, look_y, 8, half * 0.45)
        ox, oy = yellow_orb_position(enemy)
        ox, oy = ox - camera_x, oy - camera_y
        state = enemy["state"]
        if state == "charge":
            mix = min(1.0, enemy["timer"] / YELLOW_CHARGE_TIME)  # Yellow -> red as it charges
            color = (255, int(230 - 170 * mix), int(70 - 20 * mix))
            radius = YELLOW_ORB_RADIUS * (1 + 0.3 * mix)
        else:
            color = (255, 230, 70)
            radius = YELLOW_ORB_RADIUS * (min(1.0, enemy["timer"] / YELLOW_REGROW_TIME) if state == "regrow" else 1.0)
        if radius < 1:
            continue
        glow = pygame.Surface((90, 90), pygame.SRCALPHA)
        if state != "charge":
            for k in range(1, 5):  # A short motion trail behind the spinning orb
                back = enemy["orb_angle"] - k * 0.22
                tx = cx + math.cos(back) * YELLOW_ORB_DISTANCE - ox + 45
                ty = cy + math.sin(back) * YELLOW_ORB_DISTANCE - oy + 45
                pygame.draw.circle(glow, (255, 220, 60, 90 - k * 20), (tx, ty), max(1, radius - k))
        else:
            mix = min(1.0, enemy["timer"] / YELLOW_CHARGE_TIME)
            pulse = 0.5 + 0.5 * math.sin(t * (10 + 30 * mix))  # Pulses faster as it gets ready to throw
            pygame.draw.circle(glow, (255, 60, 40, int(60 + 120 * mix * pulse)), (45, 45), radius + 8 + 14 * mix)
        pygame.draw.circle(glow, (*color, 90), (45, 45), radius + 9)
        screen.blit(glow, (ox - 45, oy - 45))
        pygame.draw.circle(screen, color, (ox, oy), radius)
        pygame.draw.circle(screen, WHITE, (ox, oy), max(1, radius // 2))

# ---- Block Defence: the metal block and its repair menu ----
def create_metal_block(size):
    """Brushed steel crate: bevelled edges, cross braces, rivets and a glowing core slot."""
    surf = pygame.Surface((size, size), pygame.SRCALPHA)
    for y in range(size):  # Vertical steel gradient
        shade = int(150 - 55 * y / size)
        pygame.draw.line(surf, (shade, shade + 4, shade + 10), (0, y), (size, y))
    rng = random.Random(7)
    for _ in range(size * 2):  # Brushed streaks
        y = rng.randrange(size)
        x = rng.randrange(size)
        tone = rng.choice((18, -18))
        base = surf.get_at((x, y))
        c = tuple(max(0, min(255, v + tone)) for v in base[:3])
        pygame.draw.line(surf, c, (x, y), (min(size, x + rng.randint(8, 30)), y))
    edge = 12
    pygame.draw.rect(surf, (200, 206, 214), (0, 0, size, size), 3)                     # Bright outer rim
    pygame.draw.rect(surf, (55, 60, 70), (edge, edge, size - 2 * edge, size - 2 * edge), 3)  # Inner bevel
    pygame.draw.line(surf, (215, 220, 228), (3, 3), (size - 4, 3), 2)                   # Top highlight
    pygame.draw.line(surf, (40, 44, 52), (3, size - 4), (size - 4, size - 4), 3)          # Bottom shadow
    for a, b in (((edge, edge), (size - edge, size - edge)), ((size - edge, edge), (edge, size - edge))):
        pygame.draw.line(surf, (70, 75, 86), a, b, 9)   # Cross braces
        pygame.draw.line(surf, (125, 130, 142), a, b, 3)
    for x in (edge // 2 + 1, size - edge // 2 - 2):  # Rivets
        for y in (edge // 2 + 1, size - edge // 2 - 2):
            pygame.draw.circle(surf, (45, 48, 56), (x, y), 4)
            pygame.draw.circle(surf, (215, 220, 228), (x - 1, y - 1), 2)
    return surf

metal_block_sprite = create_metal_block(BLOCK_DEFENCE_BLOCK_W)

def block_health_color(fraction):
    """Green when healthy, yellow at half, red when nearly broken."""
    if fraction > 0.5:
        t = (fraction - 0.5) * 2
        return (int(255 - 175 * t), 225, int(60 + 20 * t))
    t = fraction * 2
    return (255, int(60 + 165 * t), 60)

def draw_block_defence_block():
    rect = BLOCK_DEFENCE_BLOCK_RECT.move(-camera_x, -camera_y)
    fraction = max(0.0, block_health / BLOCK_MAX_HEALTH)
    color = block_health_color(fraction)
    pulse = 0.5 + 0.5 * math.sin(pygame.time.get_ticks() / 250)
    glow = pygame.Surface((rect.width + 60, rect.height + 60), pygame.SRCALPHA)  # Coloured glow shows its health
    pygame.draw.rect(glow, (*color, int(40 + 40 * pulse)), glow.get_rect(), border_radius=30)
    screen.blit(glow, (rect.x - 30, rect.y - 30))
    shadow = pygame.Surface(rect.size, pygame.SRCALPHA)
    shadow.fill((0, 0, 0, 90))
    screen.blit(shadow, rect.move(8, 10))
    screen.blit(metal_block_sprite, rect)
    core = pygame.Rect(0, 0, rect.width // 3, rect.width // 3)  # Glowing core in the middle
    core.center = rect.center
    pygame.draw.rect(screen, (25, 28, 34), core.inflate(8, 8), border_radius=8)
    pygame.draw.rect(screen, color, core, border_radius=6)
    pygame.draw.rect(screen, (255, 255, 255), core.inflate(-core.width // 2, -core.height // 2), border_radius=4)
    if block_hit_flash > 0:
        flash = pygame.Surface(rect.size, pygame.SRCALPHA)
        flash.fill((255, 255, 255, int(200 * block_hit_flash / 0.15)))
        screen.blit(flash, rect)
    if rect.collidepoint(pygame.mouse.get_pos()) and not game_paused:
        pygame.draw.rect(screen, (255, 240, 150), rect.inflate(8, 8), 3, border_radius=4)  # Hover: clickable
    draw_block_health_bar(pygame.Rect(rect.centerx - 110, rect.bottom + 26, 220, 34), fraction, color)

def draw_block_health_bar(bar, fraction, color, label=None):
    """Rounded glass bar with a gradient fill, a shine, tick marks and bubble-font numbers."""
    pygame.draw.rect(screen, (15, 18, 24), bar.inflate(8, 8), border_radius=bar.height // 2 + 4)
    pygame.draw.rect(screen, (200, 206, 214), bar.inflate(8, 8), 2, border_radius=bar.height // 2 + 4)
    pygame.draw.rect(screen, (45, 20, 24), bar, border_radius=bar.height // 2)
    fill_width = int(bar.width * fraction)
    if fill_width > 0:
        fill = pygame.Surface((fill_width, bar.height), pygame.SRCALPHA)
        for y in range(bar.height):
            k = 1.15 - 0.5 * y / bar.height
            pygame.draw.line(fill, tuple(min(255, int(v * k)) for v in color), (0, y), (fill_width, y))
        mask = pygame.Surface((fill_width, bar.height), pygame.SRCALPHA)
        pygame.draw.rect(mask, (255, 255, 255, 255), mask.get_rect(), border_radius=bar.height // 2)
        fill.blit(mask, (0, 0), special_flags=pygame.BLEND_RGBA_MIN)
        screen.blit(fill, bar.topleft)
    shine = pygame.Surface((bar.width - 16, bar.height // 3), pygame.SRCALPHA)
    pygame.draw.rect(shine, (255, 255, 255, 70), shine.get_rect(), border_radius=6)
    screen.blit(shine, (bar.x + 8, bar.y + 4))
    for k in range(1, 5):
        x = bar.x + bar.width * k // 5
        pygame.draw.line(screen, (0, 0, 0, 120), (x, bar.y + 6), (x, bar.bottom - 6), 1)
    if label is None:
        label = f"{max(0, block_health)} / {BLOCK_MAX_HEALTH}"
    label = get_bubble_text(label, 30, (255, 255, 255), color, outline=5)
    screen.blit(label, label.get_rect(center=bar.center))

def open_block_menu():
    global block_menu_open, block_menu_was_paused, game_paused
    block_menu_was_paused = game_paused
    block_menu_open = True
    game_paused = True

def close_block_menu():
    global block_menu_open, game_paused
    block_menu_open = False
    game_paused = block_menu_was_paused

def block_menu_layout():
    width, height = 560, 500
    resting_y = HEIGHT // 2 - height // 2
    y = -height + (height + resting_y) * ease_out_back(min(1.0, block_menu_anim))
    panel = pygame.Rect(WIDTH // 2 - width // 2, y, width, height)
    buttons = [pygame.Rect(panel.x + 40, panel.y + 190 + i * 76, width - 80, 62) for i in range(len(BLOCK_REPAIRS))]
    close = pygame.Rect(panel.centerx - 90, panel.bottom - 60, 180, 46)
    return panel, buttons, close

def draw_block_menu():
    shade = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    shade.fill((0, 0, 0, int(150 * min(1.0, block_menu_anim))))
    screen.blit(shade, (0, 0))
    panel, buttons, close = block_menu_layout()
    pygame.draw.rect(screen, (22, 26, 34), panel, border_radius=16)  # Solid backing so the world doesn't show through
    draw_panel(panel)
    title = get_bubble_text("Block Repair", 56, (220, 235, 255), (120, 150, 190))
    screen.blit(title, title.get_rect(center=(panel.centerx, panel.y + 48)))
    fraction = max(0.0, block_health / BLOCK_MAX_HEALTH)
    draw_block_health_bar(pygame.Rect(panel.centerx - 180, panel.y + 100, 360, 36), fraction, block_health_color(fraction))
    points = get_bubble_text(f"P: {block_defence_points}", 34, (200, 255, 255), (60, 190, 255), outline=5)
    screen.blit(points, points.get_rect(center=(panel.centerx, panel.y + 160)))
    for (health, cost), button in zip(BLOCK_REPAIRS, buttons):
        full = block_health >= BLOCK_MAX_HEALTH
        affordable = block_defence_points >= cost and not full
        draw_button(button, GREEN if affordable else DARK_RED)
        name = "Full Repair" if health >= BLOCK_MAX_HEALTH else f"+{health} Health"
        name_text = button_font.render(name, True, BLACK)
        screen.blit(name_text, name_text.get_rect(midleft=(button.x + 22, button.centery)))
        cost_text = button_font.render("Full" if full else f"{cost} P", True, BLACK)
        screen.blit(cost_text, cost_text.get_rect(midright=(button.right - 22, button.centery)))
    draw_button(close, BLUE)
    close_text = button_font.render("Close", True, BLACK)
    screen.blit(close_text, close_text.get_rect(center=close.center))

def handle_block_menu_event(event):
    global block_health, block_defence_points
    if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
        close_block_menu()
        return
    if event.type != pygame.MOUSEBUTTONDOWN or event.button != 1 or block_menu_anim < 0.9:
        return
    pos = pygame.mouse.get_pos()
    _, buttons, close = block_menu_layout()
    if close.collidepoint(pos):
        close_block_menu()
        return
    for (health, cost), button in zip(BLOCK_REPAIRS, buttons):
        if button.collidepoint(pos) and block_defence_points >= cost and block_health < BLOCK_MAX_HEALTH:
            if net_role() == "guest":
                net.relay({"k": MULTIPLAYER_REPAIR_REQUEST, "i": BLOCK_REPAIRS.index((health, cost))}, to=net.lobby["host"])
                sounds.play("buy")
                continue
            block_defence_points -= cost
            sounds.play("buy")
            block_health = min(BLOCK_MAX_HEALTH, block_health + health)

def living_players():
    """Top-left positions of every player still alive in this game: you, plus the others in a multiplayer match."""
    found = [] if game_over else [(player_x, player_y)]
    if multiplayer_match:
        found += [(p["x"], p["y"]) for p in remote_players.values() if not p.get("dead")]
    return found or [(player_x, player_y)]

def nearest_player(x=None, y=None):
    """The living player closest to (x, y) (top-left positions). With no position: you if alive."""
    players = living_players()
    if x is None or len(players) == 1:
        return players[0]
    return min(players, key=lambda p: (p[0] - x) ** 2 + (p[1] - y) ** 2)

def enemy_target(ex=None, ey=None):
    """Where an enemy at (ex, ey) heads (top-left position like theirs): the block in Block Defence,
    otherwise the nearest living player."""
    if in_block_defence:
        return BLOCK_DEFENCE_BLOCK_RECT.centerx - player_size / 2, BLOCK_DEFENCE_BLOCK_RECT.centery - player_size / 2
    return nearest_player(ex, ey)

def damage_block(amount=1):
    global block_health, block_hit_flash
    sounds.play("block_damage", 0.7)
    block_health = max(0, block_health - amount)
    block_hit_flash = 0.15

BLOCK_ORANGE_RANGE = 230      # Oranges plant themselves this close to the block's center
BLOCK_ORANGE_TICK = 1 / 3     # 3 damage a second, taken off 1 at a time

def ray_to_rect(x, y, angle, rect):
    """Distance along the ray from (x, y) to where it enters rect, or None if it misses."""
    dx, dy = math.cos(angle), math.sin(angle)
    t_near, t_far = -math.inf, math.inf
    for origin, d, low, high in ((x, dx, rect.left, rect.right), (y, dy, rect.top, rect.bottom)):
        if abs(d) < 1e-9:
            if not low <= origin <= high:
                return None
            continue
        t1, t2 = (low - origin) / d, (high - origin) / d
        t_near, t_far = max(t_near, min(t1, t2)), min(t_far, max(t1, t2))
    if t_near > t_far or t_far < 0:
        return None
    return max(0.0, t_near)

def player_safe():
    """True when nothing can hurt the player: invincible, or in Block Defence (only the block takes damage)."""
    return invincible or in_block_defence

# ---- Waves ----
WAVES = {
    1: {"red": 3}, 2: {"red": 5}, 3: {"red": 10}, 4: {"red": 15}, 5: {"red": 20},
    6: {"red": 5, "green": 3}, 7: {"red": 10, "green": 5}, 8: {"red": 20, "green": 5},
    9: {"red": 10, "green": 10}, 10: {"green": 15},
    11: {"red": 3, "green": 3, "blue": 1}, 12: {"red": 5, "green": 5, "blue": 2}, 13: {"green": 15, "blue": 3},
    14: {"red": 20, "green": 15, "blue": 5}, 15: {"green": 30, "blue": 3}, 16: {"red": 40, "green": 10},
    17: {"blue": 10}, 18: {"red": 30, "blue": 5}, 19: {"red": 50, "green": 25},
    20: {"boss": "red"},
    # 21-39: eased off (never more than 100 enemies)
    21: {"green": 15, "blue": 5}, 22: {"red": 10, "green": 10, "blue": 5}, 23: {"blue": 10},
    24: {"red": 10, "green": 10, "blue": 8}, 25: {"red": 40}, 26: {"green": 30}, 27: {"blue": 12},
    28: {"red": 50, "green": 10}, 29: {"red": 35, "green": 15, "blue": 6}, 30: {"red": 35, "green": 35},
    31: {"red": 20, "green": 45}, 32: {"red": 70, "blue": 5}, 33: {"green": 60}, 34: {"blue": 15},
    35: {"red": 40, "green": 35, "blue": 8}, 36: {"red": 50, "green": 45}, 37: {"green": 30, "blue": 12},
    38: {"red": 50, "blue": 15}, 39: {"green": 100},
    40: {"boss": "green"},
    # 41-59: red, green and blue only, building up to the Blue Boss
    41: {"red": 40, "green": 20, "blue": 8}, 42: {"blue": 20}, 43: {"green": 60, "blue": 10},
    44: {"red": 50, "green": 30, "blue": 12}, 45: {"red": 80, "blue": 15}, 46: {"green": 40, "blue": 18},
    47: {"blue": 25}, 48: {"red": 45, "green": 40, "blue": 15}, 49: {"green": 70, "blue": 15},
    50: {"red": 30, "green": 30, "blue": 30}, 51: {"red": 60, "blue": 20}, 52: {"blue": 35},
    53: {"red": 50, "green": 50}, 54: {"red": 20, "green": 50, "blue": 25}, 55: {"red": 60, "blue": 40},
    56: {"green": 70, "blue": 30}, 57: {"blue": 45}, 58: {"red": 40, "green": 30, "blue": 30},
    59: {"red": 30, "green": 30, "blue": 40},
    60: {"boss": "blue"},
    # 61-79: purples, then oranges (66) and yellows (71)
    61: {"purple": 5}, 62: {"purple": 5, "blue": 10}, 63: {"purple": 6, "red": 40, "blue": 15},
    64: {"purple": 8, "green": 40, "blue": 20},
    65: {"purple": 8, "red": 30, "blue": 20}, 66: {"orange": 3}, 67: {"orange": 5, "green": 50, "blue": 15},
    68: {"purple": 6, "orange": 4, "red": 40, "green": 20}, 69: {"orange": 8, "blue": 25},
    70: {"orange": 6, "purple": 6, "green": 30}, 71: {"yellow": 5}, 72: {"yellow": 6, "purple": 8, "blue": 20},
    73: {"orange": 8, "yellow": 6, "red": 50}, 74: {"purple": 10, "orange": 6, "blue": 30},
    75: {"yellow": 10, "green": 60, "blue": 10}, 76: {"orange": 10, "yellow": 8, "purple": 6, "red": 30},
    77: {"purple": 12, "yellow": 10, "blue": 25}, 78: {"orange": 12, "purple": 10, "red": 40, "green": 20},
    79: {"yellow": 12, "orange": 12, "purple": 10, "blue": 30},
    80: {"boss": "purple"},
    # 81-99: every enemy type (never more than 100)
    81: {"red": 25, "green": 25, "blue": 15, "purple": 4, "orange": 3, "yellow": 3}, 82: {"blue": 30, "orange": 6},
    83: {"green": 40, "yellow": 8, "purple": 6}, 84: {"red": 50, "blue": 20, "orange": 5, "yellow": 5},
    85: {"purple": 12, "orange": 10}, 86: {"green": 60, "blue": 15, "yellow": 8},
    87: {"blue": 35, "purple": 8, "orange": 6}, 88: {"red": 40, "green": 30, "yellow": 10, "orange": 6},
    89: {"orange": 15, "blue": 10}, 90: {"yellow": 15, "purple": 12, "red": 20},
    91: {"red": 45, "blue": 25, "orange": 8, "yellow": 8}, 92: {"green": 50, "blue": 30, "purple": 10},
    93: {"orange": 14, "yellow": 14, "green": 20}, 94: {"purple": 15, "blue": 40},
    95: {"red": 30, "green": 30, "blue": 20, "orange": 8, "yellow": 8}, 96: {"orange": 18, "purple": 12, "red": 20},
    97: {"yellow": 18, "orange": 15, "blue": 30}, 98: {"red": 35, "green": 25, "blue": 20, "purple": 8, "orange": 6, "yellow": 6},
    99: {"blue": 40, "purple": 15, "orange": 15, "yellow": 15},
    100: {"boss": "orange"},
    # 101-119: every enemy type, tougher mixes (never more than 100)
    101: {"red": 40, "green": 30, "blue": 15, "orange": 5, "yellow": 5}, 102: {"purple": 12, "blue": 30, "yellow": 8},
    103: {"orange": 16, "yellow": 12, "green": 40}, 104: {"red": 50, "blue": 25, "purple": 10, "orange": 8},
    105: {"blue": 45, "yellow": 15}, 106: {"green": 50, "purple": 14, "orange": 12},
    107: {"red": 40, "green": 20, "yellow": 16, "orange": 14}, 108: {"blue": 40, "purple": 16, "yellow": 12},
    109: {"orange": 20, "yellow": 18, "red": 30}, 110: {"red": 30, "green": 30, "blue": 20, "purple": 10, "orange": 5, "yellow": 5},
    111: {"purple": 20, "blue": 35}, 112: {"green": 45, "orange": 18, "yellow": 18},
    113: {"red": 35, "blue": 35, "purple": 12, "orange": 10}, 114: {"yellow": 22, "orange": 20, "blue": 25},
    115: {"green": 40, "blue": 30, "purple": 15, "yellow": 10}, 116: {"orange": 24, "purple": 18, "red": 30},
    117: {"blue": 50, "yellow": 20, "orange": 15}, 118: {"red": 25, "green": 25, "blue": 20, "purple": 12, "orange": 10, "yellow": 8},
    119: {"blue": 40, "purple": 20, "orange": 20, "yellow": 20},
    120: {"boss": "yellow"},
    # 121+: the Teal arrives
    121: {"teal": 5}, 122: {"teal": 8, "red": 30, "green": 20}, 123: {"teal": 10, "blue": 20, "orange": 6},
    124: {"teal": 12, "purple": 8, "yellow": 8}, 125: {"teal": 15, "red": 30, "blue": 15, "orange": 5},
    # 126+: the Pink arrives
    126: {"pink": 3}, 127: {"pink": 6, "red": 25, "green": 15}, 128: {"pink": 8, "teal": 6, "blue": 15},
    129: {"pink": 10, "orange": 6, "yellow": 6, "red": 20}, 130: {"pink": 12, "teal": 10, "purple": 6, "blue": 15},
    # 131+: the Violet arrives (wave 140 will be the Teal Boss)
    131: {"violet": 5}, 132: {"violet": 5, "red": 30, "green": 20}, 133: {"violet": 6, "blue": 20, "pink": 6},
    134: {"violet": 8, "teal": 8, "red": 25}, 135: {"violet": 8, "orange": 8, "green": 30},
    136: {"violet": 10, "yellow": 8, "pink": 8, "blue": 10}, 137: {"violet": 10, "purple": 8, "teal": 10},
    138: {"violet": 12, "red": 30, "green": 20, "blue": 15, "pink": 6}, 139: {"violet": 14, "teal": 12, "orange": 8, "yellow": 8},
    140: {"boss": "teal"},
}

def wave_spawn_counts(number):
    """What a wave spawns. Past the last wave in the table, the last normal wave repeats."""
    wave_plan = WAVES.get(number) or WAVES[max(n for n in WAVES if "boss" not in WAVES[n])]
    return {"red": 0, "green": 0, "blue": 0, "purple": 0, "orange": 0, "yellow": 0, **wave_plan}

# ---- Bosses ----
BOSS_RADIUS = (player_size // 2) * 4   # Every boss is 4 times an enemy's radius
BOSS_HEALTH = 100                      # One player shot each
MINION_GROUPS = {"red": lambda: red_enemies, "green": lambda: green_enemies, "blue": lambda: blue_enemies}

def spawn_minions(counts):
    """Spawn a boss's helpers, e.g. {"green": 25, "red": 15}."""
    for kind, count in counts.items():
        for _ in range(count):
            MINION_GROUPS[kind]().append(get_safe_enemy_spawn())
            if kind == "blue":
                blue_last_shot_times.append(pygame.time.get_ticks() / 1000)

def minions_alive(kinds):
    return any(MINION_GROUPS[kind]() for kind in kinds)
BOSSES = {
    # kind: name, orb colour, bar colours, walking speed, which enemies it calls in
    "red": {"name": "RED BOSS", "color": (225, 35, 35), "title": ((255, 220, 200), (230, 40, 40)), "bar": (235, 50, 45),
            "speed": 0.6, "minions": {"red": 25}, "minimap": (255, 60, 50), "reward": 100},
    "green": {"name": "GREEN BOSS", "color": (80, 215, 60), "title": ((225, 255, 210), (60, 190, 50)), "bar": (90, 220, 70),
              "speed": red_enemy_speed, "minions": {"green": 25, "red": 15}, "minimap": (110, 240, 80), "reward": 100},
    "blue": {"name": "BLUE BOSS", "color": (45, 95, 245), "title": ((215, 230, 255), (50, 110, 245)), "bar": (70, 130, 255),
             "speed": 0.0, "minions": {"blue": 15, "red": 30, "green": 20}, "minimap": (80, 140, 255), "reward": 300},
    "purple": {"name": "PURPLE BOSS", "color": (150, 60, 215), "title": ((240, 215, 255), (150, 60, 215)), "bar": (170, 90, 235),
               "speed": 0.0, "minions": {}, "minimap": (180, 100, 240), "reward": 500},
    "orange": {"name": "ORANGE BOSS", "color": (255, 140, 30), "title": ((255, 235, 200), (255, 130, 20)), "bar": (255, 150, 40),
               "speed": 0.0, "minions": {}, "minimap": (255, 160, 60), "reward": 750},
    "yellow": {"name": "YELLOW BOSS", "color": (245, 215, 40), "title": ((255, 250, 200), (240, 200, 30)), "bar": (250, 220, 60),
               "speed": 0.0, "minions": {}, "minimap": (250, 225, 60), "reward": 1000},
    "teal": {"name": "TEAL BOSS", "color": (40, 215, 200), "title": ((210, 255, 250), (30, 190, 175)), "bar": (60, 225, 210),
             "speed": 0.0, "minions": {}, "minimap": (70, 235, 220), "reward": 1500, "health": 200},
}
# Orange Boss: four laser guns on a turret, in four stages, with a shielded laser-lines event at 75, 50 and 25.
YELLOW_BOSS_ORB_DISTANCE = BOSS_RADIUS + 70
YELLOW_BOSS_ORB_RADIUS = 30
YELLOW_BOSS_THROW_EVERY = 1.5     # Seconds between big orb throws
YELLOW_BOSS_REGROW = 0.8          # Thrown orbs grow back in this long (before the next throw)
YELLOW_BOSS_THROW_SPEED = 8       # Pixels per frame (straight, no curve)
YELLOW_BOSS_SPIN = math.radians(200)  # His orbs always orbit him at this speed
# Stage 2 (75-50): no spinning. 4 orbs appear and slowly drift straight out; each next ring is turned another
# 30 degrees around the circle, so there are no safe spots - but there's still room to slide between them.
YELLOW_RING_EVERY = 0.9                # Seconds between rings
YELLOW_SPIRAL_OUT = 2.5                # How fast the rings drift outward (pixels per frame)
YELLOW_BOSS_MINIONS = 30          # Yellows at 75
YELLOW_BARRAGE_TOTAL = 100        # Orbs in the barrage at 50...
YELLOW_BARRAGE_PER_VOLLEY = 10    # ...10 at a time...
YELLOW_BARRAGE_EVERY = 0.3        # ...in quick bursts
YELLOW_BARRAGE_SPEED = 8
YELLOW_BARRAGE_BOUNCES = 3        # Bounces off the barrier this many times, then breaks
YELLOW_BARRAGE_WARNING = 2.0      # At 50: all his orbs are cleared, then a 2 second warning before the barrage
YELLOW_FAST_THROW_SPEED = 13      # Stage 3 and 4 (below 50): the stage 1 throws, but faster...
YELLOW_FAST_THROW_BOUNCES = 3     # ...and bouncing off the barrier this many times
YELLOW_BOSS_SPAWN_AT_25 = {"orange": 10, "yellow": 10}
YELLOW_ARM_SPACING = 64           # Stage 4: two lines of orbs, one orb every this many pixels...
YELLOW_ARM_GROW = 700             # ...growing out this many pixels per second until they reach the barrier...
YELLOW_ARM_SPIN = math.radians(35)  # ...then sweeping around him at this speed
YELLOW_ARM_WARNING = 2.0          # Seconds of warning showing where the lines will be before they grow
TEAL_BOSS_START_WAIT = 3.0       # Visible in the middle for this long at the start
TEAL_BOSS_VANISH_WAIT = 1.0      # Invisible for this long before each teleport
TEAL_BOSS_FUSE = 1.0             # Flashes this long after appearing on the player, then explodes
TEAL_BOSS_BLAST_RADIUS = 230     # Room to run: you walk about 300 pixels in that second
TEAL_BOSS_SPAWN_AT_175 = {"pink": 10, "blue": 20, "teal": 15}
TEAL_BOSS_TEALS = 50             # Normal teals he calls in after his 3 second start, and again after the 175 shield
TEAL_SWARM_ROUNDS = 25           # At 150: this many rounds...
TEAL_SWARM_SIZE = 100            # ...of this many teals all over the map...
TEAL_SWARM_FUSE = 1.0            # ...that start flashing as they appear and explode after this long
TEAL_SWARM_GAP = 0.35            # Breather between rounds
TEAL_BOSS_THROW_EVERY = 1.5      # Below 150: stays in the middle and throws teals this often...
TEAL_BOSS_THROW_COUNT = 3        # ...this many at a time...
TEAL_BOSS_THROW_SCATTER = 170    # ...each aimed at a random spot within this far of the player
TEAL_THROWN_SPEED = 900          # Pixels per second a thrown teal flies (straight, no curve)
TEAL_BOSS_SPAWN_AT_125 = {"orange": 30, "green": 20}
ORANGE_BOSS_GUN_LENGTH = BOSS_RADIUS + 60
ORANGE_BOSS_BEAM_WIDTH = 16
ORANGE_BOSS_STAGES = {
    # guns: how many fire at once ("all" = all four always on); windup: warning glow before firing;
    # sweep: seconds per quarter turn while firing; reverse: seconds between direction changes (0 = never);
    # oranges: spawn 2 oranges every 3 seconds (max 10 alive); spawn: enemies called in once when the stage starts
    1: {"guns": 1, "windup": 0.5, "sweep": 1.7, "reverse": 0, "oranges": False, "spawn": {"purple": 10}},   # 100-75
    2: {"guns": 2, "windup": 0.4, "sweep": 1.4, "reverse": 0, "oranges": False, "spawn": {"purple": 10}},   # 75-50
    3: {"guns": "all", "windup": 1.0, "sweep": 2.0, "reverse": 10, "oranges": False, "spawn": {"red": 20}},  # 50-25
    4: {"guns": "all", "windup": 1.0, "sweep": 1.3, "reverse": 5, "oranges": False,
        "spawn": {"red": 40}},                                                   # 25-0
}
ORANGE_BOSS_ORANGE_EVERY = 3.0
ORANGE_BOSS_ORANGE_COUNT = 2
ORANGE_BOSS_ORANGE_MAX = 10
# The laser-lines events: which directions take turns, how many rounds, and how fast (1 = normal, 0.5 = twice as quick)
ORANGE_LINES_EVENTS = {
    75: {"patterns": ["h"], "rounds": 10, "speed": 1.0},
    50: {"patterns": ["h", "v"], "rounds": 15, "speed": 1.0},
    25: {"patterns": ["h", "v", "dl", "dr"], "rounds": 20, "speed": 0.5, "first_warning": 3.0},  # The first warning lasts 3 s
}
LINE_NORMALS = {"h": (0.0, 1.0), "v": (1.0, 0.0), "dl": (math.sqrt(0.5), math.sqrt(0.5)), "dr": (math.sqrt(0.5), -math.sqrt(0.5))}
ORANGE_LINES_SPACING = 150        # Gap between lines (room to stand between them)
ORANGE_LINES_STEP = 45            # How far the lines move each round (under half the gap, so they clearly move)
ORANGE_LINES_WARNING = 1.0        # Flashing warning before the lines fire
ORANGE_LINES_ACTIVE = 0.5         # How long the lines are deadly
ORANGE_LINES_GAP = 0.25           # Short breather between rounds
ORANGE_LINES_WIDTH = 30
PURPLE_ORB_HEALTH = 25
PURPLE_ORB_RADIUS = 34
PURPLE_ORB_DISTANCE = BOSS_RADIUS + 110
PURPLE_ORB_SPIN = math.radians(20)       # Slow
PURPLE_ORB_BREAK_SPAWNS = [{"red": 30}, {"red": 15, "green": 15}, {"green": 30}, {"blue": 15}]  # 1st, 2nd, 3rd, 4th orb broken
PURPLE_BOSS_RED_EVERY = 2.0             # Once he can be hit, a red appears this often...
PURPLE_BOSS_RED_MAX = 30                # ...while there are fewer than this many reds
PURPLE_BOSS_WAVE = {"blue": 10, "red": 15, "green": 8}   # At 75, 50 and 25 (halved from 20/30/15)
PURPLE_BOSS_TETHERED = 10               # Purples tied to the boss at 50 and 25 (must die before he can be hurt)
purple_boss_orb_sprite = create_orb_sprite((175, 85, 235), PURPLE_ORB_RADIUS, glow=8)
BLUE_BOSS_START_DELAY = 5.0       # Waits this long before it starts spinning and shooting
BLUE_BOSS_SHIELD_AT = (75, 50, 25)
BLUE_BOSS_SHIELD_MINIONS = [{"blue": 15}, {"blue": 10, "red": 30}, {"blue": 15, "red": 20, "green": 20}]  # At 75, 50, 25
BLUE_BOSS_GUN_LENGTH = BOSS_RADIUS + 72
# (turn speed, seconds between shots) for each stage: before 50, 50-25, below 25 (Gun V fire rate, slow turn)
BLUE_BOSS_STAGES = [(math.radians(70), 0.8 / 1.5), (math.radians(125), 0.4 / 1.5), (math.radians(70), GUN_SHOT_DELAYS[5] / 1.5)]  # Below 25: Gun V-ish fire rate, spinning twice as fast as before
BOSS_ORBS = {kind: create_orb_sprite(info["color"], BOSS_RADIUS, glow=18) for kind, info in BOSSES.items()}
GREEN_DASH_EVERY = 10.0     # Seconds of walking between dashes
GREEN_AIM_TIME = 2.0        # Shows its path this long before dashing
GREEN_REST_TIME = 2.0       # Stands still this long after a dash
GREEN_DASH_LENGTH = 900     # How far a dash goes (cut short by the barrier)
GREEN_DASH_SPEED = 2600     # Pixels per second: really fast
active_boss = None
boss_push = [0.0, 0.0]      # The player's slide velocity after being shoved out of the boss's spawn

def spawn_boss(kind):
    """The boss appears in the middle of the map. If the player is standing there, they get slid out of the way."""
    global active_boss
    sounds.play("boss_spawn")
    cx, cy = MAP_WIDTH / 2, MAP_HEIGHT / 2
    max_health = BOSSES[kind].get("health", BOSS_HEALTH)  # 100 for the first six bosses, 200 from the Teal Boss on
    active_boss = {"kind": kind, "x": cx, "y": cy, "health": max_health, "max_health": max_health, "enraged": False, "flash": 0.0, "grace": 0.0,
                   "state": "chase", "timer": GREEN_DASH_EVERY, "angle": 0.0, "dash_left": 0.0, "trail": [],
                   "start": BLUE_BOSS_START_DELAY, "shielded": False, "shields_used": 0, "shot_timer": 0.0, "ripple": 0.0}
    if kind == "purple":
        shielded = set(random.sample(range(4), 3))  # One orb starts open, the other three are shielded
        active_boss["orbs"] = [{"angle": k * math.pi / 2, "health": PURPLE_ORB_HEALTH, "shielded": k in shielded,
                                "ripple": 0.0, "flash": 0.0} for k in range(4)]
        active_boss["events_done"] = []   # Which of 75 / 50 / 25 have happened
        active_boss["tethered"] = False   # True while the tied-on purples are alive
        active_boss["shielded"] = True
    if kind == "teal":
        active_boss.update({"phase": "start", "timer": TEAL_BOSS_START_WAIT, "blink_phase": 0.0, "events_done": []})
    if kind == "yellow":
        active_boss.update({"slots": [1.0, 1.0, 1.0, 1.0], "spin": 0.0, "throw_timer": YELLOW_BOSS_THROW_EVERY,
                            "events_done": [], "event": None, "barrage_fired": 0, "barrage_timer": 0.0,
                            "arms": None})
    if kind == "orange":
        active_boss.update({"stage": 1, "firing": [], "phase": "windup", "phase_time": 0.0, "turret": 0.0,
                            "direction": 1, "reverse_timer": 0.0, "orange_timer": 0.0, "lines": None,
                            "events_done": []})
        orange_boss_enter_stage(active_boss, 1)
    px, py = player_x + player_size / 2, player_y + player_size / 2
    if math.hypot(px - cx, py - cy) < BOSS_RADIUS + player_size:
        a = random.uniform(0, 2 * math.pi)
        boss_push[:] = [math.cos(a) * 26, math.sin(a) * 26]
        active_boss["grace"] = 1.0  # Can't hurt the player while they slide out

def boss_dash_length(boss):
    """How far the dash can go before the boss would hit the barrier."""
    return max(0.0, min(GREEN_DASH_LENGTH, laser_reach(boss["x"], boss["y"], boss["angle"]) - BOSS_RADIUS))

def update_boss(dt):
    global player_x, player_y
    # The slide out of the boss's spawn (never kills)
    if abs(boss_push[0]) + abs(boss_push[1]) > 0.2:
        player_x += boss_push[0]
        player_y += boss_push[1]
        boss_push[0] *= 0.9
        boss_push[1] *= 0.9
    else:
        boss_push[:] = [0.0, 0.0]
    boss = active_boss
    if boss is None:
        return
    info = BOSSES[boss["kind"]]
    boss["flash"] = max(0.0, boss["flash"] - dt)
    boss["ripple"] = max(0.0, boss["ripple"] - dt)
    boss["grace"] = max(0.0, boss["grace"] - dt)
    px, py = player_x + player_size / 2, player_y + player_size / 2
    target_x, target_y = nearest_player(boss["x"] - player_size / 2, boss["y"] - player_size / 2)
    tx, ty = target_x + player_size / 2, target_y + player_size / 2
    frozen = has_freeze and equipped_ability == 'freeze' and freeze_active
    boss["trail"] = [(x, y, age + dt) for x, y, age in boss["trail"] if age + dt < 0.35]
    if not frozen:
        if boss["kind"] == "green":
            update_green_boss(boss, dt, tx, ty)
        elif boss["kind"] == "blue":
            update_blue_boss(boss, dt)
        elif boss["kind"] == "purple":
            update_purple_boss(boss, dt)
        elif boss["kind"] == "orange":
            update_orange_boss(boss, dt)
        elif boss["kind"] == "yellow":
            update_yellow_boss(boss, dt)
        elif boss["kind"] == "teal":
            update_teal_boss(boss, dt)
        else:
            distance = math.hypot(tx - boss["x"], ty - boss["y"])
            if distance > 1:
                boss["x"] += (tx - boss["x"]) / distance * info["speed"]
                boss["y"] += (ty - boss["y"]) / distance * info["speed"]
    if boss["kind"] in ("red", "green") and boss["enraged"] and not minions_alive(info["minions"]):
        spawn_minions(info["minions"])  # At half health, and again whenever they've all been killed
    touching = math.hypot(px - boss["x"], py - boss["y"]) < BOSS_RADIUS + player_size / 2 - 6
    if boss["kind"] == "teal":
        touching = False  # He lands right on you on purpose - only his explosion hurts
    if touching and not game_over and not player_safe() and boss["grace"] == 0 and boss_push == [0.0, 0.0]:
        player_hit()

def purple_boss_orb_position(boss, orb):
    return (boss["x"] + math.cos(orb["angle"]) * PURPLE_ORB_DISTANCE, boss["y"] + math.sin(orb["angle"]) * PURPLE_ORB_DISTANCE)

def update_purple_boss(boss, dt):
    """Stays in the middle while its orbs slowly circle it (he never moves). It can't be hurt while any orb is left, or while the
    purples tied to it (at 50 and 25) are alive. Whenever he can be hurt, a red spawns every 2 seconds (max 30)."""
    for orb in boss["orbs"]:
        orb["angle"] = (orb["angle"] + PURPLE_ORB_SPIN * dt) % (2 * math.pi)
        orb["ripple"] = max(0.0, orb["ripple"] - dt)
        orb["flash"] = max(0.0, orb["flash"] - dt)
    if boss["tethered"] and not purple_enemies:
        boss["tethered"] = False
    boss["shielded"] = bool(boss["orbs"]) or boss["tethered"]
    if not boss["shielded"]:  # He never moves; whenever he can be hit, a red appears every 2 seconds (up to 30)
        boss["red_timer"] = boss.get("red_timer", 0.0) + dt
        if boss["red_timer"] >= PURPLE_BOSS_RED_EVERY:
            boss["red_timer"] = 0.0
            if len(red_enemies) < PURPLE_BOSS_RED_MAX:
                red_enemies.append(get_safe_enemy_spawn())

def kill_all_enemies_no_coins():
    """Every normal enemy bursts apart, with no coins (used by the Purple Boss)."""
    for kind, group in (("red", red_enemies), ("green", green_enemies), ("blue", blue_enemies), ("purple", purple_enemies)):
        for ex, ey in group:
            spawn_death_effect(ex + player_size // 2, ey + player_size // 2, kind)
        group.clear()
    for minis in purple_mini_circles:
        for mini_x, mini_y, _ in minis:
            spawn_death_effect(mini_x, mini_y, "purple_mini")
    purple_mini_circles.clear()
    blue_last_shot_times.clear()
    for kind, group in dict_enemy_groups():
        for enemy in group:
            spawn_death_effect(enemy["x"] + player_size // 2, enemy["y"] + player_size // 2, kind)
        group.clear()

def spawn_tied_purples(boss):
    """The purples tied to the boss appear in a ring close around him (not scattered across the map, where one could
    take ages to walk back into view). Any spot too close to the player is pushed further out."""
    barrier = 12
    offset = random.uniform(0, 2 * math.pi)
    px, py = player_x + player_size / 2, player_y + player_size / 2
    for k in range(PURPLE_BOSS_TETHERED):
        a = offset + k * 2 * math.pi / PURPLE_BOSS_TETHERED
        radius = BOSS_RADIUS + 150
        for _ in range(4):
            cx, cy = boss["x"] + math.cos(a) * radius, boss["y"] + math.sin(a) * radius
            if math.hypot(cx - px, cy - py) > 220:
                break
            radius += 160
        # Keep it where you can see it (inside the view, with room for its minis), and inside the barrier
        view_left, view_top = px - WIDTH / 2 + 90, py - HEIGHT / 2 + 90
        cx = max(view_left, min(view_left + WIDTH - 180, cx))
        cy = max(view_top, min(view_top + HEIGHT - 180, cy))
        ex = max(barrier, min(MAP_WIDTH - player_size - barrier, cx - player_size / 2))
        ey = max(barrier, min(MAP_HEIGHT - player_size - barrier, cy - player_size / 2))
        purple_enemies.append([ex, ey])
        purple_mini_circles.append([[0, 0, j * math.pi / 2] for j in range(4)])
        update_purple_minis(len(purple_enemies) - 1)

def purple_boss_event(boss, at):
    """At 75: 20 blue, 30 red, 15 green. At 50 and 25: everything left dies, then the same again plus 10 purples tied to him."""
    boss["events_done"].append(at)
    if at in (50, 25):
        kill_all_enemies_no_coins()
        spawn_tied_purples(boss)
        boss["tethered"] = True
        boss["shielded"] = True
        boss["ripple"] = 0.4
    spawn_minions(PURPLE_BOSS_WAVE)

def purple_boss_take_bullet(boss, bullet):
    """A player shot near the Purple Boss: orbs first (shields splash it off), then his body. True if the shot is used up."""
    bx, by = bullet["x"] + bullet_size / 2, bullet["y"] + bullet_size / 2
    for orb in boss["orbs"]:
        ox, oy = purple_boss_orb_position(boss, orb)
        reach = PURPLE_ORB_RADIUS + (22 if orb["shielded"] else 0)
        if math.hypot(bx - ox, by - oy) < reach:
            if orb["shielded"]:
                orb["ripple"] = 0.25
                return True
            orb["health"] -= 1
            orb["flash"] = 0.08
            if orb["health"] <= 0:
                for _ in range(4):
                    spawn_death_effect(ox + random.uniform(-15, 15), oy + random.uniform(-15, 15), "purple")
                boss["orbs"].remove(orb)
                spawn_minions(PURPLE_ORB_BREAK_SPAWNS[min(3, 3 - len(boss["orbs"]))])
                still_shielded = [o for o in boss["orbs"] if o["shielded"]]
                if still_shielded:
                    chosen = random.choice(still_shielded)  # A random orb loses its shield
                    chosen["shielded"] = False
                    chosen["ripple"] = 0.4
                boss["shielded"] = bool(boss["orbs"]) or boss["tethered"]
            return True
    if math.hypot(bx - boss["x"], by - boss["y"]) < BOSS_RADIUS:
        hurt_boss(1)
        return True
    return False

def boss_take_bullet(bullet):
    """Let the current boss (and its parts) take a player shot. True if the shot hit something and is used up."""
    if active_boss is None:
        return False
    if active_boss["kind"] == "purple":
        return purple_boss_take_bullet(active_boss, bullet)
    if active_boss["kind"] == "teal" and not teal_boss_visible(active_boss):
        return False  # Invisible: shots go straight through where he was
    if active_boss["kind"] == "yellow":
        bx, by = bullet["x"] + bullet_size / 2, bullet["y"] + bullet_size / 2
        for k in range(4):  # His orbiting orbs block shots
            if active_boss["slots"][k] > 0.3:
                ox, oy = yellow_boss_slot_position(active_boss, k)
                if math.hypot(bx - ox, by - oy) < YELLOW_BOSS_ORB_RADIUS * active_boss["slots"][k] + 4:
                    spawn_shot_clash(bx, by)
                    return True
        if active_boss["arms"] is not None:  # So do the orbs in his lines
            for ox, oy in yellow_arm_orbs(active_boss):
                if math.hypot(bx - ox, by - oy) < YELLOW_BOSS_ORB_RADIUS + 4:
                    spawn_shot_clash(bx, by)
                    return True
    if bullet_hits_boss(bullet):
        if net_role() == "guest":
            active_boss["flash"] = 0.08  # The host's game takes the health off
        else:
            hurt_boss(1)
        return True
    return False

def yellow_boss_slot_position(boss, k):
    angle = boss["spin"] + k * math.pi / 2 + boss.get("slot_offset", 0.0)
    return boss["x"] + math.cos(angle) * YELLOW_BOSS_ORB_DISTANCE, boss["y"] + math.sin(angle) * YELLOW_BOSS_ORB_DISTANCE

def yellow_arm_orbs(boss):
    """World positions of every orb in his two lines (one line each way from him)."""
    arms = boss["arms"]
    orbs = []
    for side in (0, math.pi):
        angle = arms["angle"] + side
        reach = min(arms["length"], laser_reach(boss["x"], boss["y"], angle) - YELLOW_BOSS_ORB_RADIUS)
        d = BOSS_RADIUS + YELLOW_BOSS_ORB_RADIUS + 20
        while d <= reach:
            orbs.append((boss["x"] + math.cos(angle) * d, boss["y"] + math.sin(angle) * d))
            d += YELLOW_ARM_SPACING
    return orbs

def update_yellow_arms(boss, dt):
    """Stage 4: the lines grow out until both reach the barrier, then sweep around him. Touching one kills you."""
    arms = boss["arms"]
    if not arms["full"]:
        arms["length"] += YELLOW_ARM_GROW * dt
        longest = max(laser_reach(boss["x"], boss["y"], arms["angle"]), laser_reach(boss["x"], boss["y"], arms["angle"] + math.pi))
        if arms["length"] >= longest:
            arms["full"] = True
    else:
        arms["length"] = math.hypot(MAP_WIDTH, MAP_HEIGHT)  # Always reaching the barrier while it sweeps
        arms["angle"] = (arms["angle"] + YELLOW_ARM_SPIN * dt) % (2 * math.pi)
    if not game_over and not player_safe():
        px, py = player_x + player_size / 2, player_y + player_size / 2
        for ox, oy in yellow_arm_orbs(boss):
            if math.hypot(px - ox, py - oy) < YELLOW_BOSS_ORB_RADIUS + player_size / 2 - 4:
                player_hit()
                break

def yellow_barrage_left():
    return sum(1 for b in blue_bullets if b.get("barrage"))

def update_yellow_boss(boss, dt):
    """Stays in the middle. 100-75: 4 orbs orbit him and every 1.5 s all 4 fly straight out. At 75: shield + 30 yellows.
    75-50: no spinning, rings of 4 drift out, each turned another 30 degrees. At 50: orbs cleared, shield, 2 s warning,
    then 100 bouncing orbs. 50-25: stage 1 throws, faster and bouncing. At 25: 50 blue + 25 orange. 25-0: the same
    throws plus two lines of orbs that grow to the barrier and then sweep around him."""
    for k in range(4):
        boss["slots"][k] = min(1.0, boss["slots"][k] + dt / YELLOW_BOSS_REGROW)
    stage2 = 75 in boss["events_done"] and 50 not in boss["events_done"]  # Rings, no spinning
    fast = 50 in boss["events_done"]  # Stages 3 and 4: stage 1 throws, faster and bouncing
    if boss["arms"] is not None:
        update_yellow_arms(boss, dt)
    if not stage2 or boss["shielded"]:  # His orbs orbit him (not while throwing rings in stage 2 - but yes while shielded)
        boss["spin"] = (boss["spin"] + YELLOW_BOSS_SPIN * dt) % (2 * math.pi)
    if not game_over and not player_safe():  # Touching one of his orbs (before it's thrown) kills you too
        px, py = player_x + player_size / 2, player_y + player_size / 2
        for k in range(4):
            if boss["slots"][k] > 0.5:
                ox, oy = yellow_boss_slot_position(boss, k)
                if math.hypot(px - ox, py - oy) < YELLOW_BOSS_ORB_RADIUS * boss["slots"][k] + player_size / 2 - 4:
                    player_hit()
                    break
    event = boss["event"]
    if event == "enemies25":
        if not (red_enemies or green_enemies or blue_enemies or purple_enemies or orange_enemies or yellow_enemies or teal_enemies or pink_enemies or violet_enemies):
            boss["event"], boss["shielded"], boss["ripple"] = "arms_warning", False, 0.4
            boss["arms_warning"] = {"angle": random.uniform(0, math.pi), "time": 0.0}
        return
    if event == "arms_warning":
        warning = boss["arms_warning"]
        warning["time"] += dt
        if warning["time"] >= YELLOW_ARM_WARNING:
            boss["arms"] = {"angle": warning["angle"], "length": 0.0, "full": False}  # Grow exactly where the warning was
            boss["event"] = None
        return
    if event == "yellows":
        if not yellow_enemies:
            boss["event"], boss["shielded"], boss["ripple"] = None, False, 0.4
        return
    if event == "barrage":
        boss["barrage_timer"] -= dt
        if boss["barrage_fired"] < YELLOW_BARRAGE_TOTAL and boss["barrage_timer"] <= 0:
            boss["barrage_timer"] = YELLOW_BARRAGE_EVERY
            offset = boss["barrage_fired"] / YELLOW_BARRAGE_PER_VOLLEY * math.radians(18)  # Each burst is turned a little
            size = player_size  # Normal enemy sized
            for k in range(min(YELLOW_BARRAGE_PER_VOLLEY, YELLOW_BARRAGE_TOTAL - boss["barrage_fired"])):
                angle = offset + k * 2 * math.pi / YELLOW_BARRAGE_PER_VOLLEY
                sx = boss["x"] + math.cos(angle) * (BOSS_RADIUS + 40) - size / 2
                sy = boss["y"] + math.sin(angle) * (BOSS_RADIUS + 40) - size / 2
                blue_bullets.append({"x": sx, "y": sy, "dx": math.cos(angle) * YELLOW_BARRAGE_SPEED, "dy": math.sin(angle) * YELLOW_BARRAGE_SPEED,
                                     "scale": size / bullet_size, "orb": True, "orb_color": "yellow", "tough": True,
                                     "bounces": YELLOW_BARRAGE_BOUNCES, "barrage": True})
            boss["barrage_fired"] += min(YELLOW_BARRAGE_PER_VOLLEY, YELLOW_BARRAGE_TOTAL - boss["barrage_fired"])
        if boss["barrage_fired"] >= YELLOW_BARRAGE_TOTAL and yellow_barrage_left() == 0:
            boss["event"], boss["shielded"], boss["ripple"] = None, False, 0.4
        return
    boss["throw_timer"] -= dt
    if boss["throw_timer"] <= 0:
        px, py = player_x + player_size / 2, player_y + player_size / 2
        size = YELLOW_BOSS_ORB_RADIUS * 2
        speed = YELLOW_SPIRAL_OUT if stage2 else YELLOW_FAST_THROW_SPEED if fast else YELLOW_BOSS_THROW_SPEED
        if not stage2:
            boss["slot_offset"] = 0.0
        for k in range(4):  # All 4 orbs go at the same time, straight out from him
            ox, oy = yellow_boss_slot_position(boss, k)
            out = boss["spin"] + k * math.pi / 2 + boss.get("slot_offset", 0.0)
            shot = {"x": ox - size / 2, "y": oy - size / 2, "scale": size / bullet_size, "orb": True,
                    "orb_color": "yellow", "tough": True, "ring": stage2,
                    "dx": math.cos(out) * speed, "dy": math.sin(out) * speed}
            if fast:
                shot["bounces"] = YELLOW_FAST_THROW_BOUNCES
            blue_bullets.append(shot)
            boss["slots"][k] = 0.0
        boss["ring"] = boss.get("ring", 0) + 1
        if stage2:
            # Each new ring is turned another 30 degrees (0, 30, 60, 0...), so over three rings every direction gets covered
            boss["slot_offset"] = (boss.get("slot_offset", 0.0) + math.radians(30)) % (math.pi / 2)
        boss["throw_timer"] = YELLOW_RING_EVERY if stage2 else YELLOW_BOSS_THROW_EVERY

def yellow_boss_event(boss, at):
    boss["health"] = at
    boss["events_done"].append(at)
    boss["shielded"], boss["ripple"] = True, 0.4
    if at == 25:
        # Shield up while 10 oranges and 10 yellows are alive; then a 2 s warning, then his two lines of orbs
        boss["event"] = "enemies25"
        for shot in [b for b in blue_bullets if b.get("orb") and b.get("tough")]:  # Clear every orb still flying or bouncing
            spawn_shot_clash(shot["x"] + shot_size(shot) / 2, shot["y"] + shot_size(shot) / 2)
            blue_bullets.remove(shot)
        spawn_minions_any(YELLOW_BOSS_SPAWN_AT_25)
        return
    if at == 75:
        boss["event"] = "yellows"
        spawn_minions_any({"yellow": YELLOW_BOSS_MINIONS})
    elif at == 50:
        boss["event"] = "barrage"
        boss["barrage_fired"], boss["barrage_timer"] = 0, YELLOW_BARRAGE_WARNING
        for shot in [b for b in blue_bullets if b.get("orb") and b.get("tough")]:  # Clear every orb already out
            spawn_shot_clash(shot["x"] + shot_size(shot) / 2, shot["y"] + shot_size(shot) / 2)
            blue_bullets.remove(shot)

def update_teal_boss(boss, dt):
    """3 s in the middle, then 50 teals come in and the loop starts: invisible for 1 s -> appears on top of the player ->
    flashes faster and faster -> explodes (he survives) -> invisible again. At 175 he waits shielded in the middle until
    every enemy is dead, then 50 more teals and back to the loop."""
    boss["timer"] -= dt
    if boss["phase"] == "swarm":
        update_teal_swarm(boss, dt)
        return
    if boss["phase"] == "throw":
        if boss["timer"] <= 0:
            teal_boss_throw(boss)
            boss["timer"] = TEAL_BOSS_THROW_EVERY
        return
    if boss["phase"] == "guard":
        # Shielded in the middle until every enemy is dead. After 175: 50 more teals and back to teleporting.
        # After 125: back to throwing teals.
        if not any_enemies_alive():
            boss["shielded"], boss["ripple"] = False, 0.4
            if boss.get("guard_at", 175) == 175:
                spawn_minions_any({"teal": TEAL_BOSS_TEALS})
                boss["phase"], boss["timer"] = "hidden", TEAL_BOSS_VANISH_WAIT
            else:
                boss["phase"], boss["timer"] = "throw", 0.6
        return
    if boss["phase"] == "start":
        if boss["timer"] <= 0:
            spawn_minions_any({"teal": TEAL_BOSS_TEALS})  # 50 teals come in as he starts his loop
            boss["phase"], boss["timer"] = "hidden", TEAL_BOSS_VANISH_WAIT
    elif boss["phase"] == "hidden":
        if boss["timer"] <= 0:
            # Teleport right onto a player (any living one, in multiplayer)
            victim_x, victim_y = random.choice(living_players())
            boss["x"], boss["y"] = victim_x + player_size / 2, victim_y + player_size / 2
            boss["fuse_len"] = teal_boss_fuse(boss)
            boss["phase"], boss["timer"], boss["blink_phase"] = "fuse", boss["fuse_len"], 0.0
            effects.append({"type": "flash", "x": boss["x"], "y": boss["y"], "age": 0.0, "life": 0.3, "color": (80, 255, 235), "size": 2.0})
    elif boss["phase"] == "fuse":
        progress = 1 - max(0.0, boss["timer"]) / boss["fuse_len"]
        boss["blink_phase"] += (4 + 18 * progress) * dt  # Flashes speed up
        if boss["timer"] <= 0:
            teal_boss_explode(boss)
            boss["phase"], boss["timer"] = "hidden", TEAL_BOSS_VANISH_WAIT

def teal_boss_explode(boss):
    sounds.play("teal_explode")
    effects.append({"type": "flash", "x": boss["x"], "y": boss["y"], "age": 0.0, "life": 0.55, "color": (60, 255, 230), "size": 5.5})
    for _ in range(6):
        a = random.uniform(0, 2 * math.pi)
        r = random.uniform(0, TEAL_BOSS_BLAST_RADIUS * 0.6)
        spawn_death_effect(boss["x"] + math.cos(a) * r, boss["y"] + math.sin(a) * r, "teal")
    px, py = player_x + player_size / 2, player_y + player_size / 2
    if not game_over and not player_safe() and math.hypot(px - boss["x"], py - boss["y"]) < TEAL_BOSS_BLAST_RADIUS + player_size / 2:
        player_hit()

def teal_boss_visible(boss):
    """Whether he can be seen (and shot). Fading away after a hit doesn't count."""
    return boss["phase"] in ("start", "fuse", "swarm", "guard", "throw")

def any_enemies_alive():
    return bool(red_enemies or green_enemies or blue_enemies or purple_enemies or orange_enemies or yellow_enemies
                or teal_enemies or pink_enemies or violet_enemies)

def teal_boss_start_guard(boss, at=175):
    """At 175 and 125: any enemies still alive die (no coins), he shields up in the middle, and that point's
    enemies come in (175: 10 pink, 20 blue, 15 teal - 125: 30 orange, 20 green). The shield stays until they're all dead."""
    kill_all_enemies_no_coins()
    boss["events_done"].append(at)
    boss["health"] = at
    boss["x"], boss["y"] = MAP_WIDTH / 2, MAP_HEIGHT / 2
    effects.append({"type": "flash", "x": boss["x"], "y": boss["y"], "age": 0.0, "life": 0.4, "color": (80, 255, 235), "size": 3.0})
    boss["phase"], boss["timer"], boss["guard_at"] = "guard", 0.0, at
    boss["shielded"], boss["ripple"] = True, 0.4
    spawn_minions_any(TEAL_BOSS_SPAWN_AT_175 if at == 175 else TEAL_BOSS_SPAWN_AT_125)

def teal_boss_fuse(boss):
    return TEAL_BOSS_FUSE

def teal_boss_throw(boss):
    """Throw 3 teals, already ticking, each flying straight to a random spot scattered around the player."""
    half = player_size / 2
    for _ in range(TEAL_BOSS_THROW_COUNT):
        victim_x, victim_y = random.choice(living_players())  # Each teal lands near one of the players
        px, py = victim_x + half, victim_y + half
        a = random.uniform(0, 2 * math.pi)
        r = random.uniform(0, TEAL_BOSS_THROW_SCATTER)
        teal = new_teal_enemy(boss["x"] - half, boss["y"] - half)
        teal.update({"fuse": 0.0, "fuse_len": TEAL_FUSE, "thrown_to": (px + math.cos(a) * r - half, py + math.sin(a) * r - half)})
        teal_enemies.append(teal)

def teal_boss_start_swarm(boss):
    """At 150: every other enemy dies (no coins), he jumps to the middle behind a shield, and the swarm rounds begin."""
    kill_all_enemies_no_coins()
    boss["events_done"].append(150)
    boss["health"] = 150
    boss["x"], boss["y"] = MAP_WIDTH / 2, MAP_HEIGHT / 2
    effects.append({"type": "flash", "x": boss["x"], "y": boss["y"], "age": 0.0, "life": 0.4, "color": (80, 255, 235), "size": 3.0})
    boss["phase"], boss["timer"] = "swarm", 1.0  # A second to see where he went before the first round
    boss["swarm_round"] = 0
    boss["shielded"], boss["ripple"] = True, 0.4

def update_teal_swarm(boss, dt):
    if any(e.get("swarm") for e in teal_enemies):
        boss["timer"] = TEAL_SWARM_GAP  # The breather starts once this round has all exploded
        return
    if boss["timer"] > 0:
        return
    if boss["swarm_round"] >= TEAL_SWARM_ROUNDS:
        # All rounds done: shield drops, and he stays in the middle throwing teals at the player
        boss["shielded"], boss["ripple"] = False, 0.4
        boss["phase"], boss["timer"] = "throw", 0.6
        return
    boss["swarm_round"] += 1
    barrier = 12
    for _ in range(TEAL_SWARM_SIZE):  # Scattered all over the map, already flashing
        x = random.uniform(barrier, MAP_WIDTH - player_size - barrier)
        y = random.uniform(barrier, MAP_HEIGHT - player_size - barrier)
        teal = new_teal_enemy(x, y)
        teal.update({"fuse": 0.0, "fuse_len": TEAL_SWARM_FUSE, "swarm": True})
        teal_enemies.append(teal)
    boss["timer"] = TEAL_SWARM_GAP

def orange_boss_stage_for(health):
    return 1 if health > 75 else 2 if health > 50 else 3 if health > 25 else 4

def orange_boss_enter_stage(boss, stage):
    """Start a gun stage: pick the first guns, reset the timers and call in that stage's enemies."""
    config = ORANGE_BOSS_STAGES[stage]
    boss["stage"], boss["lines"], boss["shielded"] = stage, None, False
    boss["phase"], boss["phase_time"] = "windup", 0.0
    boss["reverse_timer"], boss["orange_timer"] = 0.0, 0.0
    boss["firing"] = orange_boss_pick_guns(config, [])
    spawn_minions_any(config["spawn"])

def spawn_minions_any(counts):
    """Like spawn_minions, but also handles oranges and purples."""
    for kind, count in counts.items():
        if kind == "orange":
            for _ in range(count):
                orange_enemies.append(new_orange_enemy(*get_safe_enemy_spawn()))
        elif kind == "purple":
            for _ in range(count):
                spawn_purple()
        elif kind == "yellow":
            for _ in range(count):
                yellow_enemies.append(new_yellow_enemy(*get_safe_enemy_spawn()))
        elif kind == "teal":
            for _ in range(count):
                teal_enemies.append(new_teal_enemy(*get_safe_enemy_spawn()))
        elif kind == "pink":
            for _ in range(count):
                pink_enemies.append(new_pink_enemy(*get_safe_enemy_spawn()))
        elif kind == "violet":
            for _ in range(count):
                violet_enemies.append(new_violet_enemy(*get_safe_enemy_spawn()))
        else:
            spawn_minions({kind: count})

def orange_boss_pick_guns(config, previous):
    if config["guns"] == "all":
        return [0, 1, 2, 3]
    choices = [k for k in range(4) if k not in previous] or list(range(4))
    if len(choices) < config["guns"]:
        choices = list(range(4))
    return random.sample(choices, config["guns"])

def orange_boss_beams(boss):
    """(start x, start y, angle, length) for every beam that's firing right now."""
    if boss["lines"] is not None or boss["phase"] != "sweep":
        return []
    beams = []
    for gun in boss["firing"]:
        angle = boss["turret"] + gun * math.pi / 2
        sx = boss["x"] + math.cos(angle) * ORANGE_BOSS_GUN_LENGTH
        sy = boss["y"] + math.sin(angle) * ORANGE_BOSS_GUN_LENGTH
        beams.append((sx, sy, angle, laser_reach(sx, sy, angle)))
    return beams

def orange_boss_beam(boss):
    beams = orange_boss_beams(boss)
    return beams[0] if beams else None

def orange_lines_offsets(lines, pattern_round):
    """Shift for this round: the lines creep along a little every round."""
    return (pattern_round * ORANGE_LINES_STEP) % ORANGE_LINES_SPACING

def orange_lines_current(boss):
    """(normal x, normal y, shift) of this round's lines."""
    lines = boss["lines"]
    event = ORANGE_LINES_EVENTS[lines["at"]]
    pattern = event["patterns"][lines["round"] % len(event["patterns"])]
    nx, ny = LINE_NORMALS[pattern]
    return nx, ny, orange_lines_offsets(lines, lines["round"])

def orange_lines_rows(boss):
    """World y of every horizontal line this round (used by older code and tests)."""
    nx, ny, shift = orange_lines_current(boss)
    first = ORANGE_LINES_SPACING / 2 - shift
    return [first + k * ORANGE_LINES_SPACING for k in range(int(MAP_HEIGHT // ORANGE_LINES_SPACING) + 2)
            if 0 < first + k * ORANGE_LINES_SPACING < MAP_HEIGHT]

def orange_line_distance(px, py, nx, ny, shift):
    """How far a point is from the nearest line of a set (lines sit at n.p = spacing/2 - shift + k * spacing)."""
    d = (px * nx + py * ny - (ORANGE_LINES_SPACING / 2 - shift)) % ORANGE_LINES_SPACING
    return min(d, ORANGE_LINES_SPACING - d)

def update_orange_boss(boss, dt):
    px, py = player_x + player_size / 2, player_y + player_size / 2
    if boss["lines"] is not None:
        update_orange_lines(boss, dt, px, py)
        return
    config = ORANGE_BOSS_STAGES[boss["stage"]]
    turn_speed = (math.pi / 2) / config["sweep"]
    if config["reverse"]:
        boss["reverse_timer"] += dt
        if boss["reverse_timer"] >= config["reverse"]:
            boss["reverse_timer"] = 0.0
            boss["direction"] *= -1  # Switches which way it spins
    boss["turret"] += turn_speed * boss["direction"] * dt  # The turret never stops turning
    boss["phase_time"] += dt
    if boss["phase"] == "windup" and boss["phase_time"] >= config["windup"]:
        boss["phase"], boss["phase_time"] = "sweep", 0.0
    elif boss["phase"] == "sweep" and config["guns"] != "all" and boss["phase_time"] >= config["sweep"]:
        # Right when the beams stop, other random guns glow their warning and fire next
        boss["firing"] = orange_boss_pick_guns(config, boss["firing"])
        boss["phase"], boss["phase_time"] = "windup", 0.0
    if config["oranges"]:
        boss["orange_timer"] += dt
        if boss["orange_timer"] >= ORANGE_BOSS_ORANGE_EVERY:
            boss["orange_timer"] = 0.0
            for _ in range(min(ORANGE_BOSS_ORANGE_COUNT, ORANGE_BOSS_ORANGE_MAX - len(orange_enemies))):
                orange_enemies.append(new_orange_enemy(*get_safe_enemy_spawn()))
    if not game_over and not player_safe():
        for sx, sy, angle, length in orange_boss_beams(boss):
            if shield_stops_laser(sx, sy, angle, length) is not None:
                continue
            ex, ey = sx + math.cos(angle) * length, sy + math.sin(angle) * length
            if point_to_segment_distance(px, py, sx, sy, ex, ey) < player_size / 2 + ORANGE_BOSS_BEAM_WIDTH / 2:
                player_hit()
                break

def update_orange_lines(boss, dt, px, py):
    lines = boss["lines"]
    event = ORANGE_LINES_EVENTS[lines["at"]]
    speed = event["speed"]
    lines["time"] += dt
    if lines["phase"] == "warning" and lines["time"] >= orange_lines_warning_time(lines):
        lines["phase"], lines["time"] = "active", 0.0
    elif lines["phase"] == "active":
        if not game_over and not player_safe():
            nx, ny, shift = orange_lines_current(boss)
            if orange_line_distance(px, py, nx, ny, shift) < player_size / 2 + ORANGE_LINES_WIDTH / 2:
                player_hit()
        if lines["time"] >= ORANGE_LINES_ACTIVE * speed:
            lines["phase"], lines["time"] = "gap", 0.0
    elif lines["phase"] == "gap" and lines["time"] >= ORANGE_LINES_GAP * speed:
        lines["round"] += 1
        if lines["round"] >= event["rounds"]:
            # All rounds done: the shield drops and the next gun stage starts
            boss["ripple"] = 0.4
            orange_boss_enter_stage(boss, orange_boss_stage_for(boss["health"]) if boss["health"] < lines["at"] else
                                    {75: 2, 50: 3, 25: 4}[lines["at"]])
        else:
            lines["phase"], lines["time"] = "warning", 0.0

def orange_lines_warning_time(lines):
    """How long this round's warning lasts: normally ORANGE_LINES_WARNING (sped up by the event), but an event can
    make its very first warning longer (3 s at 25) so there's time to get ready."""
    event = ORANGE_LINES_EVENTS[lines["at"]]
    if lines["round"] == 0 and event.get("first_warning"):
        return event["first_warning"]
    return ORANGE_LINES_WARNING * event["speed"]

def orange_boss_start_lines(boss, at=75):
    """At 75, 50 and 25: every enemy dies (no coins), the shield goes up and the laser lines start."""
    boss["health"] = at
    boss["events_done"].append(at)
    kill_all_enemies_no_coins()
    boss["lines"] = {"at": at, "round": 0, "phase": "warning", "time": 0.0}
    boss["shielded"], boss["ripple"] = True, 0.4
    boss["phase"], boss["phase_time"] = "windup", 0.0

def update_blue_boss(boss, dt):
    """Stays in the middle. After 5 seconds it spins and fires red lasers from its gun. At 75, 50 and 25 it
    shields up (can't be hurt) and calls in enemies; when they're all dead it goes back to spinning and shooting."""
    if boss["shielded"]:
        if not minions_alive(("red", "green", "blue")):
            boss["shielded"] = False
        return
    if boss["start"] > 0:
        boss["start"] -= dt
        return
    turn, delay = BLUE_BOSS_STAGES[max(0, boss["shields_used"] - 1)]
    boss["angle"] = (boss["angle"] + turn * dt) % (2 * math.pi)
    boss["shot_timer"] -= dt
    if boss["shot_timer"] <= 0:
        boss["shot_timer"] = delay
        dx, dy = math.cos(boss["angle"]), math.sin(boss["angle"])
        size = bullet_size * BLUE_BOSS_SHOT_SCALE
        blue_bullets.append({"x": boss["x"] + dx * BLUE_BOSS_GUN_LENGTH - size / 2,
                             "y": boss["y"] + dy * BLUE_BOSS_GUN_LENGTH - size / 2,
                             "dx": dx * blue_bullet_speed, "dy": dy * blue_bullet_speed, "scale": BLUE_BOSS_SHOT_SCALE})
        boss["muzzle"] = pygame.time.get_ticks() / 1000

def update_green_boss(boss, dt, px, py):
    """Walk -> stop and show the dash path -> dash -> rest. Below 25 health it skips the walking."""
    furious = boss["health"] <= BOSS_HEALTH // 4
    if boss["state"] == "chase":
        distance = math.hypot(px - boss["x"], py - boss["y"])
        if distance > 1:
            boss["x"] += (px - boss["x"]) / distance * BOSSES["green"]["speed"]
            boss["y"] += (py - boss["y"]) / distance * BOSSES["green"]["speed"]
        boss["timer"] -= dt
        if boss["timer"] <= 0 or furious:
            boss["state"], boss["timer"] = "aim", GREEN_AIM_TIME
            boss["angle"] = math.atan2(py - boss["y"], px - boss["x"])  # Locks in where the player is now
            boss["dash_left"] = boss_dash_length(boss)
    elif boss["state"] == "aim":
        boss["timer"] -= dt
        if boss["timer"] <= 0:
            boss["state"] = "dash"
    elif boss["state"] == "dash":
        step = min(boss["dash_left"], GREEN_DASH_SPEED * dt)
        boss["trail"].append((boss["x"], boss["y"], 0.0))
        boss["x"] += math.cos(boss["angle"]) * step
        boss["y"] += math.sin(boss["angle"]) * step
        boss["dash_left"] -= step
        if boss["dash_left"] <= 0.5:
            if boss["health"] <= BOSS_HEALTH // 4:
                # Below 25: no rest - straight into lining up the next dash
                boss["state"], boss["timer"] = "aim", GREEN_AIM_TIME
                boss["angle"] = math.atan2(py - boss["y"], px - boss["x"])
                boss["dash_left"] = boss_dash_length(boss)
            else:
                boss["state"], boss["timer"] = "rest", GREEN_REST_TIME
    elif boss["state"] == "rest":
        boss["timer"] -= dt
        if boss["timer"] <= 0:
            boss["state"], boss["timer"] = "chase", GREEN_DASH_EVERY

def hurt_boss(amount=1, force=False):
    """Take health off the boss; at half it starts calling in its enemies, and at zero it bursts and takes them with it.
    force (the kill cheat) ignores the Blue Boss's shield."""
    global active_boss, kills
    boss = active_boss
    info = BOSSES[boss["kind"]]
    if boss["kind"] == "blue" and not force:
        if boss["shielded"]:
            boss["ripple"] = 0.25  # The shot splashes off the shield
            sounds.play("shield_block", 0.6)
            return
        boss["health"] -= amount
        boss["flash"] = 0.08
        if boss["shields_used"] < len(BLUE_BOSS_SHIELD_AT) and boss["health"] <= BLUE_BOSS_SHIELD_AT[boss["shields_used"]]:
            boss["health"] = BLUE_BOSS_SHIELD_AT[boss["shields_used"]]
            boss["shields_used"] += 1
            boss["shielded"] = True
            boss["ripple"] = 0.4
            spawn_minions(BLUE_BOSS_SHIELD_MINIONS[boss["shields_used"] - 1])
        amount = 0
    if boss["kind"] == "teal" and not force:
        if boss["shielded"]:
            boss["ripple"] = 0.25
            sounds.play("shield_block", 0.6)
            return
        boss["health"] -= amount
        boss["flash"] = 0.08
        if boss["health"] <= 175 and 175 not in boss["events_done"] and boss["health"] > 0:
            teal_boss_start_guard(boss)
        elif boss["health"] <= 150 and 150 not in boss["events_done"] and boss["health"] > 0:
            teal_boss_start_swarm(boss)
        elif boss["health"] <= 125 and 125 not in boss["events_done"] and boss["health"] > 0:
            teal_boss_start_guard(boss, 125)
        amount = 0
    if boss["kind"] == "yellow" and not force:
        if boss["shielded"]:
            boss["ripple"] = 0.25
            sounds.play("shield_block", 0.6)
            return
        boss["health"] -= amount
        boss["flash"] = 0.08
        for at in (75, 50, 25):
            if boss["health"] <= at and at not in boss["events_done"] and boss["health"] > 0:
                yellow_boss_event(boss, at)
                break
        amount = 0
    if boss["kind"] == "orange" and not force:
        if boss["shielded"]:
            boss["ripple"] = 0.25
            sounds.play("shield_block", 0.6)
            return
        boss["health"] -= amount
        boss["flash"] = 0.08
        for at in (75, 50, 25):
            if boss["health"] <= at and at not in boss["events_done"] and boss["health"] > 0:
                orange_boss_start_lines(boss, at)
                break
        amount = 0
    if boss["kind"] == "purple" and not force:
        if boss["shielded"]:
            boss["ripple"] = 0.25  # Orbs or tied-on purples still alive: shots splash off
            sounds.play("shield_block", 0.6)
            return
        boss["health"] -= amount
        boss["flash"] = 0.08
        for at in (75, 50, 25):
            if boss["health"] <= at and at not in boss["events_done"] and boss["health"] > 0:
                boss["health"] = at
                purple_boss_event(boss, at)
                break
        amount = 0
    boss["health"] -= amount
    boss["flash"] = 0.08
    sounds.play("boss_hit", 0.5)
    if boss["health"] <= BOSS_HEALTH // 2 and not boss["enraged"]:
        boss["enraged"] = True
    if boss["health"] <= 0:
        shard_kind = boss["kind"]
        for _ in range(6):
            a = random.uniform(0, 2 * math.pi)
            r = random.uniform(0, BOSS_RADIUS * 0.7)
            spawn_death_effect(boss["x"] + math.cos(a) * r, boss["y"] + math.sin(a) * r, shard_kind)
        sounds.play("boss_death")
        spawn_death_effect(boss["x"], boss["y"], shard_kind)  # No coin: boss waves pay out when the wave completes
        for kind in info["minions"]:  # Its helpers all go with it
            for ex, ey in MINION_GROUPS[kind]():
                spawn_death_effect(ex + player_size // 2, ey + player_size // 2, kind)
            MINION_GROUPS[kind]().clear()
            if kind == "blue":
                blue_last_shot_times.clear()
        if boss["kind"] in ("purple", "orange", "yellow", "teal"):
            kill_all_enemies_no_coins()  # Everything left dies with him
        active_boss = None
        kills += 1

def bullet_hits_boss(bullet):
    return active_boss is not None and math.hypot(bullet["x"] + bullet_size / 2 - active_boss["x"],
                                                  bullet["y"] + bullet_size / 2 - active_boss["y"]) < BOSS_RADIUS

def draw_green_dash_path(boss, cx, cy):
    """See-through green lane showing where the dash will go: it fills up as the dash gets closer,
    with arrows racing along it and a ghost of the boss where it will stop."""
    length = boss["dash_left"]
    if length < 1:
        return
    charge = 1 - max(0.0, boss["timer"]) / GREEN_AIM_TIME  # 0 -> 1 over the aim time
    t = pygame.time.get_ticks() / 1000
    dx, dy = math.cos(boss["angle"]), math.sin(boss["angle"])
    nx, ny = -dy, dx
    w = BOSS_RADIUS
    layer = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    def lane(start, end, half_width):
        return [(cx + dx * start + nx * half_width, cy + dy * start + ny * half_width),
                (cx + dx * end + nx * half_width, cy + dy * end + ny * half_width),
                (cx + dx * end - nx * half_width, cy + dy * end - ny * half_width),
                (cx + dx * start - nx * half_width, cy + dy * start - ny * half_width)]
    pygame.draw.polygon(layer, (80, 255, 90, 45), lane(0, length, w))                      # Whole lane, faint
    pygame.draw.polygon(layer, (120, 255, 110, int(60 + 50 * charge)), lane(0, length * charge, w))  # Filling up
    for side in (1, -1):  # Glowing edges
        edge = [(cx + nx * w * side, cy + ny * w * side), (cx + dx * length + nx * w * side, cy + dy * length + ny * w * side)]
        pygame.draw.line(layer, (10, 40, 10, 110), *edge, 10)  # Dark outline so it reads on grass too
        pygame.draw.line(layer, (170, 255, 160, int(150 + 100 * charge)), *edge, 4)
    spacing = 90
    for k in range(int(length // spacing) + 1):  # Chevrons racing toward the end
        d = (k * spacing + (t * 420) % spacing)
        if d > length - 20:
            continue
        tip = (cx + dx * (d + 26), cy + dy * (d + 26))
        wing = w * 0.45
        pts = [(cx + dx * d + nx * wing, cy + dy * d + ny * wing), tip, (cx + dx * d - nx * wing, cy + dy * d - ny * wing)]
        pygame.draw.lines(layer, (210, 255, 200, int(90 + 120 * charge)), False, pts, 6)
    end_x, end_y = cx + dx * length, cy + dy * length
    pulse = 0.5 + 0.5 * math.sin(t * 14)
    pygame.draw.circle(layer, (120, 255, 110, int(40 + 40 * pulse)), (end_x, end_y), w)       # Ghost where it lands
    pygame.draw.circle(layer, (10, 40, 10, 110), (end_x, end_y), w + 3, 10)
    pygame.draw.circle(layer, (200, 255, 190, int(160 + 90 * charge)), (end_x, end_y), w, 4)
    screen.blit(layer, (0, 0))

def draw_boss():
    boss = active_boss
    if boss is None:
        return
    if boss["kind"] == "teal":
        draw_teal_boss(boss)
        return
    info = BOSSES[boss["kind"]]
    cx, cy = boss["x"] - camera_x, boss["y"] - camera_y
    if boss["kind"] == "green" and boss["state"] == "aim":
        draw_green_dash_path(boss, cx, cy)
        cx += random.uniform(-3, 3) * (1 - boss["timer"] / GREEN_AIM_TIME)  # Shakes as it winds up
        cy += random.uniform(-3, 3) * (1 - boss["timer"] / GREEN_AIM_TIME)
    if boss["trail"]:  # Afterimages and speed streaks behind a dash
        layer = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
        for x, y, age in boss["trail"]:
            fade = 1 - age / 0.35
            pygame.draw.circle(layer, (*info["color"], int(90 * fade)), (x - camera_x, y - camera_y), BOSS_RADIUS * (0.6 + 0.4 * fade))
        tail_x, tail_y, _ = boss["trail"][0]
        for off in (-0.6, -0.2, 0.2, 0.6):
            ox, oy = -math.sin(boss["angle"]) * BOSS_RADIUS * off, math.cos(boss["angle"]) * BOSS_RADIUS * off
            pygame.draw.line(layer, (230, 255, 220, 150), (tail_x - camera_x + ox, tail_y - camera_y + oy),
                             (boss["x"] - camera_x + ox, boss["y"] - camera_y + oy), 3)
        screen.blit(layer, (0, 0))
    shadow = pygame.Surface((BOSS_RADIUS * 2, BOSS_RADIUS), pygame.SRCALPHA)
    pygame.draw.ellipse(shadow, (0, 0, 0, 80), shadow.get_rect())
    screen.blit(shadow, (cx - BOSS_RADIUS + 14, cy + BOSS_RADIUS * 0.55))
    if boss["enraged"]:  # Angry pulsing aura once it's at half health
        pulse = 0.5 + 0.5 * math.sin(pygame.time.get_ticks() / 120)
        aura = pygame.Surface((BOSS_RADIUS * 3, BOSS_RADIUS * 3), pygame.SRCALPHA)
        pygame.draw.circle(aura, (*info["bar"], int(50 + 50 * pulse)), (BOSS_RADIUS * 1.5, BOSS_RADIUS * 1.5), BOSS_RADIUS + 18 + 10 * pulse)
        screen.blit(aura, (cx - BOSS_RADIUS * 1.5, cy - BOSS_RADIUS * 1.5))
    look_x, look_y = player_x - camera_x + player_size / 2, player_y - camera_y + player_size / 2
    if boss["kind"] == "blue":
        gx, gy = math.cos(boss["angle"]), math.sin(boss["angle"])
        end = (cx + gx * BLUE_BOSS_GUN_LENGTH, cy + gy * BLUE_BOSS_GUN_LENGTH)
        pygame.draw.line(screen, (30, 34, 44), (cx, cy), end, 38)       # Big turret barrel
        pygame.draw.line(screen, (105, 115, 138), (cx, cy), end, 20)
        pygame.draw.line(screen, (170, 180, 200), (cx - gy * 4, cy + gx * 4), (end[0] - gy * 4, end[1] + gx * 4), 4)
        pygame.draw.circle(screen, (30, 34, 44), end, 22)
        pygame.draw.circle(screen, (255, 90, 80), end, 10)
        since = pygame.time.get_ticks() / 1000 - boss.get("muzzle", -9)
        if since < 0.12:
            draw_muzzle_flash(*end, (255, 90, 80), since)
        look_x, look_y = end
    if boss["kind"] == "purple":
        draw_purple_boss_strings(boss, cx, cy)
    if boss["kind"] == "orange":
        draw_orange_boss_guns(boss, cx, cy)
    if boss["kind"] == "yellow" and boss["event"] == "barrage" and boss["barrage_fired"] == 0:
        draw_yellow_barrage_warning(boss, cx, cy)
    if boss["kind"] == "yellow" and boss["event"] == "arms_warning":
        draw_yellow_arms_warning(boss, cx, cy)
    if boss["kind"] == "yellow" and boss["arms"] is not None:
        t_now = pygame.time.get_ticks() / 1000
        for ox, oy in yellow_arm_orbs(boss):
            sx, sy = ox - camera_x, oy - camera_y
            if on_screen(sx, sy, 60):
                draw_flung_orb(sx, sy, t_now, radius=YELLOW_BOSS_ORB_RADIUS, color="yellow")
    if boss["kind"] == "yellow":
        t_now = pygame.time.get_ticks() / 1000
        for k in range(4):  # His 4 big orbs orbiting him (thrown ones grow back)
            ox, oy = yellow_boss_slot_position(boss, k)
            grown = boss["slots"][k]
            if grown > 0.05:
                sx, sy = ox - camera_x, oy - camera_y
                draw_flung_orb(sx, sy, t_now, radius=max(3, int(YELLOW_BOSS_ORB_RADIUS * grown)), color="yellow")
    draw_orb(BOSS_ORBS[boss["kind"]], None, cx, cy)
    draw_eye(cx, cy, look_x, look_y, 32, BOSS_RADIUS * 0.3)
    if boss["kind"] == "purple":
        draw_purple_boss_parts(boss, cx, cy)
    if boss["kind"] in ("blue", "purple", "orange", "yellow") and (boss["shielded"] or boss["ripple"] > 0):
        draw_boss_shield(boss, cx, cy)
    if boss["flash"] > 0:
        flash = pygame.Surface((BOSS_RADIUS * 2, BOSS_RADIUS * 2), pygame.SRCALPHA)
        pygame.draw.circle(flash, (255, 255, 255, 120), (BOSS_RADIUS, BOSS_RADIUS), BOSS_RADIUS)
        screen.blit(flash, (cx - BOSS_RADIUS, cy - BOSS_RADIUS))

def draw_orange_boss_guns(boss, cx, cy):
    """Four big laser guns around the Orange Boss; guns about to fire glow as a warning, then fire to the barrier."""
    t = pygame.time.get_ticks() / 1000
    for sx, sy, angle, length in orange_boss_beams(boss):
        blocked = shield_stops_laser(sx, sy, angle, length)
        length = blocked if blocked is not None else length
        start = (sx - camera_x, sy - camera_y)
        end = (start[0] + math.cos(angle) * length, start[1] + math.sin(angle) * length)
        clipped = screen.get_rect().inflate(80, 80).clipline(start, end)
        if not clipped:
            continue
        (x1, y1), (x2, y2) = clipped
        area = pygame.Rect(min(x1, x2), min(y1, y2), abs(x2 - x1) + 1, abs(y2 - y1) + 1).inflate(80, 80).clip(screen.get_rect())
        if area.width <= 0 or area.height <= 0:
            continue
        layer = pygame.Surface(area.size, pygame.SRCALPHA)
        a = (start[0] - area.x, start[1] - area.y)
        b = (end[0] - area.x, end[1] - area.y)
        flicker = 0.85 + 0.15 * math.sin(t * 45 + angle)
        pygame.draw.line(layer, (255, 20, 20, int(110 * flicker)), a, b, 44)
        pygame.draw.line(layer, (255, 60, 40, int(230 * flicker)), a, b, 22)
        pygame.draw.line(layer, (255, 200, 180, 255), a, b, 8)
        pygame.draw.circle(layer, (255, 140, 120, 220), b, 20 * flicker)
        screen.blit(layer, area.topleft)
    config = ORANGE_BOSS_STAGES[boss["stage"]]
    for k in range(4):
        angle = boss["turret"] + k * math.pi / 2
        gx, gy = math.cos(angle), math.sin(angle)
        end = (cx + gx * ORANGE_BOSS_GUN_LENGTH, cy + gy * ORANGE_BOSS_GUN_LENGTH)
        pygame.draw.line(screen, (35, 30, 28), (cx, cy), end, 40)
        pygame.draw.line(screen, (125, 115, 105), (cx, cy), end, 20)
        pygame.draw.circle(screen, (35, 30, 28), end, 24)
        active = boss["lines"] is None and k in boss["firing"]
        if active and boss["phase"] == "windup":
            charge = min(1.0, boss["phase_time"] / config["windup"])
            glow = pygame.Surface((90, 90), pygame.SRCALPHA)
            pygame.draw.circle(glow, (255, 60, 40, int(80 + 150 * charge)), (45, 45), 12 + 30 * charge)
            screen.blit(glow, (end[0] - 45, end[1] - 45))
        pygame.draw.circle(screen, (255, 90, 60) if active else (150, 70, 50), end, 11)

def draw_orange_lines(boss):
    """Laser lines (horizontal, vertical or diagonal): a flashing, charging warning, then the deadly lines."""
    if boss["kind"] != "orange" or boss["lines"] is None or boss["lines"]["phase"] == "gap":
        return
    lines = boss["lines"]
    speed = ORANGE_LINES_EVENTS[lines["at"]]["speed"]
    t = pygame.time.get_ticks() / 1000
    nx, ny, shift = orange_lines_current(boss)
    dx, dy = -ny, nx  # Along the line
    map_rect = pygame.Rect(-camera_x, -camera_y, MAP_WIDTH, MAP_HEIGHT).clip(screen.get_rect())
    if map_rect.width <= 0 or map_rect.height <= 0:
        return
    layer = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    layer.set_clip(map_rect)  # Lines stop at the barrier
    center_x, center_y = camera_x + WIDTH / 2, camera_y + HEIGHT / 2
    half_len = math.hypot(WIDTH, HEIGHT) / 2 + 60
    base = ORANGE_LINES_SPACING / 2 - shift
    c_center = center_x * nx + center_y * ny
    first_k = math.floor((c_center - half_len - base) / ORANGE_LINES_SPACING)
    last_k = math.ceil((c_center + half_len - base) / ORANGE_LINES_SPACING)
    warning = lines["phase"] == "warning"
    blink = 1 if int(t * 10) % 2 == 0 else 0.65  # Flashing, but never too faint to see
    grow = min(1.0, lines["time"] / orange_lines_warning_time(lines)) if warning else 1.0
    flicker = 0.85 + 0.15 * math.sin(t * 50)
    for k in range(first_k, last_k + 1):
        c = base + k * ORANGE_LINES_SPACING
        # Middle of the line nearest the screen center, then out to both ends
        mx = center_x + nx * (c - c_center) - camera_x
        my = center_y + ny * (c - c_center) - camera_y
        p1 = (mx - dx * half_len, my - dy * half_len)
        p2 = (mx + dx * half_len, my + dy * half_len)
        w = ORANGE_LINES_WIDTH
        if warning:
            pygame.draw.line(layer, (0, 0, 0, 70), p1, p2, w + 6)
            pygame.draw.line(layer, (255, 70, 40, int(120 * blink)), p1, p2, w)
            charge_end = (p1[0] + dx * half_len * 2 * grow, p1[1] + dy * half_len * 2 * grow)
            pygame.draw.line(layer, (255, 170, 60, int(150 * blink)), p1, charge_end, w)  # Charging up
            for side in (-1, 1):
                ox, oy = nx * side * w / 2, ny * side * w / 2
                pygame.draw.line(layer, (255, 230, 120, int(255 * blink)), (p1[0] + ox, p1[1] + oy), (p2[0] + ox, p2[1] + oy), 3)
            step = 60
            slide = (t * 300) % step
            for s in range(int(half_len * 2 // step) + 1):  # Warning stripes sliding along the line
                along = s * step + slide
                sx, sy = p1[0] + dx * along, p1[1] + dy * along
                pygame.draw.line(layer, (255, 240, 180, int(170 * blink)), (sx + nx * 10 - dx * 10, sy + ny * 10 - dy * 10),
                                 (sx - nx * 10 + dx * 10, sy - ny * 10 + dy * 10), 4)
        else:
            pygame.draw.line(layer, (255, 20, 20, int(110 * flicker)), p1, p2, 60)
            pygame.draw.line(layer, (255, 60, 40, int(230 * flicker)), p1, p2, w)
            pygame.draw.line(layer, (255, 210, 190, 255), p1, p2, 8)
    screen.blit(layer, (0, 0))

def draw_yellow_arms_warning(boss, cx, cy):
    """The 2 seconds before his lines of orbs: flashing lanes exactly where the two lines will grow, filling up."""
    warning = boss["arms_warning"]
    t = pygame.time.get_ticks() / 1000
    charge = min(1.0, warning["time"] / YELLOW_ARM_WARNING)
    blink = 1 if int(t * 8) % 2 == 0 else 0.55
    width = YELLOW_BOSS_ORB_RADIUS * 2
    layer = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    for side in (0, math.pi):
        angle = warning["angle"] + side
        reach = laser_reach(boss["x"], boss["y"], angle)
        start = (cx + math.cos(angle) * (BOSS_RADIUS + 20), cy + math.sin(angle) * (BOSS_RADIUS + 20))
        end = (cx + math.cos(angle) * reach, cy + math.sin(angle) * reach)
        pygame.draw.line(layer, (0, 0, 0, 80), start, end, width + 8)
        pygame.draw.line(layer, (255, 190, 30, int(130 * blink)), start, end, width)
        nx, ny = -math.sin(angle) * width / 2, math.cos(angle) * width / 2
        for edge in (-1, 1):
            pygame.draw.line(layer, (255, 245, 150, int(255 * blink)), (start[0] + nx * edge, start[1] + ny * edge),
                             (end[0] + nx * edge, end[1] + ny * edge), 3)
        filled = (start[0] + (end[0] - start[0]) * charge, start[1] + (end[1] - start[1]) * charge)
        pygame.draw.line(layer, (255, 250, 200, int(220 * blink)), start, filled, 8)  # Charging out to the barrier
    screen.blit(layer, (0, 0))

def draw_yellow_barrage_warning(boss, cx, cy):
    """The 2 seconds before the barrage: flashing lanes showing where the first burst will fly, and a charging ring."""
    t = pygame.time.get_ticks() / 1000
    charge = 1 - max(0.0, boss["barrage_timer"]) / YELLOW_BARRAGE_WARNING
    blink = 1 if int(t * 8) % 2 == 0 else 0.55
    reach = math.hypot(WIDTH, HEIGHT)
    layer = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    for k in range(YELLOW_BARRAGE_PER_VOLLEY):
        angle = k * 2 * math.pi / YELLOW_BARRAGE_PER_VOLLEY
        start = (cx + math.cos(angle) * (BOSS_RADIUS + 40), cy + math.sin(angle) * (BOSS_RADIUS + 40))
        end = (cx + math.cos(angle) * reach, cy + math.sin(angle) * reach)
        pygame.draw.line(layer, (0, 0, 0, 80), start, end, int(player_size + 8))
        pygame.draw.line(layer, (255, 190, 30, int(130 * blink)), start, end, int(player_size))
        nx, ny = -math.sin(angle) * player_size / 2, math.cos(angle) * player_size / 2
        for side in (-1, 1):  # Bright edges so the lane stands out on any map
            pygame.draw.line(layer, (255, 245, 150, int(255 * blink)), (start[0] + nx * side, start[1] + ny * side),
                             (end[0] + nx * side, end[1] + ny * side), 3)
        filled = (start[0] + (end[0] - start[0]) * charge, start[1] + (end[1] - start[1]) * charge)
        pygame.draw.line(layer, (255, 250, 200, int(220 * blink)), start, filled, 8)  # Charging along the lane
    pygame.draw.circle(layer, (255, 220, 60, int(200 * blink)), (cx, cy), BOSS_RADIUS + 40 + 30 * (1 - charge), 6)
    screen.blit(layer, (0, 0))

def draw_purple_boss_strings(boss, cx, cy):
    """Energy strings from the boss to its orbs, and to the purples tied to him."""
    pulse = 0.5 + 0.5 * math.sin(pygame.time.get_ticks() / 150)
    for orb in boss["orbs"]:
        ox, oy = purple_boss_orb_position(boss, orb)
        pygame.draw.line(screen, (70, 20, 110), (cx, cy), (ox - camera_x, oy - camera_y), 12)
        pygame.draw.line(screen, (215, 150, 255), (cx, cy), (ox - camera_x, oy - camera_y), 4)
    if boss["tethered"]:
        for ex, ey in purple_enemies:
            end = (ex - camera_x + player_size / 2, ey - camera_y + player_size / 2)
            pygame.draw.line(screen, (70, 20, 110), (cx, cy), end, 7)
            pygame.draw.line(screen, (230, int(160 + 60 * pulse), 255), (cx, cy), end, 2)

def draw_purple_boss_parts(boss, cx, cy):
    """The orbs: each with its own health bar, and a shield bubble while it is protected."""
    for orb in boss["orbs"]:
        ox, oy = purple_boss_orb_position(boss, orb)
        sx, sy = ox - camera_x, oy - camera_y
        if not on_screen(sx, sy, 120):
            continue
        draw_orb(purple_boss_orb_sprite, None, sx, sy)
        draw_eye(sx, sy, player_x - camera_x + player_size / 2, player_y - camera_y + player_size / 2, 9, 6)
        if orb["flash"] > 0:
            pygame.draw.circle(screen, (255, 255, 255), (sx, sy), PURPLE_ORB_RADIUS, 0)
        if orb["shielded"] or orb["ripple"] > 0:
            draw_shield_bubble(sx, sy, PURPLE_ORB_RADIUS + 22, orb["shielded"], orb["ripple"], hex_size=9)
        bar = pygame.Rect(sx - 36, sy - PURPLE_ORB_RADIUS - 34, 72, 10)
        pygame.draw.rect(screen, (20, 12, 30), bar.inflate(4, 4), border_radius=6)
        fill = bar.copy()
        fill.width = max(0, int(bar.width * orb["health"] / PURPLE_ORB_HEALTH))
        pygame.draw.rect(screen, (150, 215, 255) if orb["shielded"] else (200, 120, 255), fill, border_radius=5)

def draw_teal_boss(boss):
    """Invisible while hiding; flashing on and off (faster and faster) with his blast circle closing in during the fuse."""
    cx, cy = boss["x"] - camera_x, boss["y"] - camera_y
    if not teal_boss_visible(boss):
        return
    visible = True
    if boss["phase"] == "fuse":
        progress = 1 - max(0.0, boss["timer"]) / boss["fuse_len"]
        r = TEAL_BOSS_BLAST_RADIUS
        ring = pygame.Surface((r * 2 + 20, r * 2 + 20), pygame.SRCALPHA)
        c = r + 10
        pygame.draw.circle(ring, (60, 255, 230, int(35 + 55 * progress)), (c, c), r)
        pygame.draw.circle(ring, (190, 255, 245, int(120 + 120 * progress)), (c, c), r, 4)
        pygame.draw.circle(ring, (190, 255, 245, 170), (c, c), max(6, r * (1 - progress)), 3)  # Closing in
        screen.blit(ring, (cx - c, cy - c))
        visible = math.sin(boss["blink_phase"] * 2 * math.pi) > 0
    if not visible:
        return
    shadow = pygame.Surface((BOSS_RADIUS * 2, BOSS_RADIUS), pygame.SRCALPHA)
    pygame.draw.ellipse(shadow, (0, 0, 0, 80), shadow.get_rect())
    screen.blit(shadow, (cx - BOSS_RADIUS + 14, cy + BOSS_RADIUS * 0.55))
    draw_orb(BOSS_ORBS["teal"], None, cx, cy)
    draw_eye(cx, cy, player_x - camera_x + player_size / 2, player_y - camera_y + player_size / 2, 32, BOSS_RADIUS * 0.3)
    if boss["flash"] > 0:
        flash = pygame.Surface((BOSS_RADIUS * 2, BOSS_RADIUS * 2), pygame.SRCALPHA)
        pygame.draw.circle(flash, (255, 255, 255, 120), (BOSS_RADIUS, BOSS_RADIUS), BOSS_RADIUS)
        screen.blit(flash, (cx - BOSS_RADIUS, cy - BOSS_RADIUS))
    if boss["shielded"] or boss["ripple"] > 0:
        draw_boss_shield(boss, cx, cy)

def draw_boss_shield(boss, cx, cy):
    draw_shield_bubble(cx, cy, BOSS_RADIUS + 38, boss["shielded"], boss["ripple"])

def draw_shield_bubble(cx, cy, r, shielded, ripple, hex_size=22):
    """Invincible look: a shimmering hexagon-patterned energy bubble with spinning arcs, and a ripple when shot."""
    t = pygame.time.get_ticks() / 1000
    size = r * 2 + 40
    layer = pygame.Surface((size, size), pygame.SRCALPHA)
    c = size / 2
    strength = 1.0 if shielded else ripple / 0.4  # Fades away when the shield drops
    pulse = 0.5 + 0.5 * math.sin(t * 5)
    pygame.draw.circle(layer, (90, 200, 255, int((45 + 25 * pulse) * strength)), (c, c), r)
    for ring in range(2):  # Honeycomb of hexagons across the bubble
        for k in range(6 + ring * 6):
            a = k / (6 + ring * 6) * 2 * math.pi + t * (0.3 if ring else -0.3)
            dist = r * (0.35 + 0.35 * ring)
            hx, hy = c + math.cos(a) * dist, c + math.sin(a) * dist
            hexagon = [(hx + math.cos(a2) * hex_size, hy + math.sin(a2) * hex_size) for a2 in (i * math.pi / 3 for i in range(6))]
            pygame.draw.polygon(layer, (170, 235, 255, int(70 * strength)), hexagon, 2)
    for k in range(3):  # Spinning bright arcs around the edge
        start = t * 2.2 + k * 2 * math.pi / 3
        pygame.draw.arc(layer, (220, 250, 255, int(230 * strength)), (c - r, c - r, r * 2, r * 2), start, start + 0.9, 6)
    pygame.draw.circle(layer, (200, 245, 255, int(200 * strength)), (c, c), r, 3)
    if ripple > 0 and shielded:
        grow = 1 - ripple / 0.4
        pygame.draw.circle(layer, (255, 255, 255, int(220 * (1 - grow))), (c, c), r - 10 + 30 * grow, 5)
    screen.blit(layer, (cx - c, cy - c))

def draw_boss_health():
    """Boss name and health bar across the top of the screen."""
    if active_boss is None:
        return
    info = BOSSES[active_boss["kind"]]
    fraction = max(0.0, active_boss["health"] / active_boss["max_health"])
    bar = pygame.Rect(WIDTH // 2 - 300, 58, 600, 34)
    title = get_bubble_text(info["name"], 44, *info["title"], outline=6)
    screen.blit(title, title.get_rect(center=(WIDTH // 2, 30)))
    if active_boss["kind"] == "yellow" and active_boss["event"] == "yellows":
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"SHIELDED - kill the yellows! ({len(yellow_enemies)} left)")
    elif active_boss["kind"] == "teal" and active_boss.get("phase") == "guard":
        left = sum(len(group) for group in (red_enemies, green_enemies, blue_enemies, purple_enemies, orange_enemies,
                                            yellow_enemies, teal_enemies, pink_enemies, violet_enemies))
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"SHIELDED - kill the enemies! ({left} left)")
    elif active_boss["kind"] == "teal" and active_boss.get("phase") == "swarm":
        rounds_left = TEAL_SWARM_ROUNDS - active_boss["swarm_round"] + (1 if any(e.get("swarm") for e in teal_enemies) else 0)
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"Dodge the teals! ({min(TEAL_SWARM_ROUNDS, rounds_left)} left)")
    elif active_boss["kind"] == "yellow" and active_boss["event"] == "enemies25":
        left = len(blue_enemies) + len(orange_enemies) + len(red_enemies) + len(green_enemies) + len(purple_enemies) + len(yellow_enemies) + len(teal_enemies) + len(pink_enemies) + len(violet_enemies)
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"SHIELDED - kill the enemies! ({left} left)")
    elif active_boss["kind"] == "yellow" and active_boss["event"] == "barrage":
        left = YELLOW_BARRAGE_TOTAL - active_boss["barrage_fired"] + yellow_barrage_left()
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"Dodge the orbs! ({left} left)")
    elif active_boss["kind"] == "orange" and active_boss["lines"] is not None:
        rounds_left = ORANGE_LINES_EVENTS[active_boss["lines"]["at"]]["rounds"] - active_boss["lines"]["round"]
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"Dodge the lasers! ({rounds_left} left)")
    elif active_boss["kind"] == "purple" and active_boss["orbs"]:
        left = len(active_boss["orbs"])
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"Break the orbs! ({left} left)")
    elif active_boss["kind"] == "purple" and active_boss["tethered"]:
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"Kill the tied purples! ({len(purple_enemies)} left)")
    elif active_boss.get("shielded"):
        draw_block_health_bar(bar, fraction, (150, 215, 255), label=f"SHIELDED - kill the blues!")
    else:
        draw_block_health_bar(bar, fraction, info["bar"], label=f"{max(0, active_boss['health'])} / {active_boss['max_health']}")

# ---- Sandbox: Add Enemies menu ----
enemy_menu_open = False
enemy_menu_anim = 0.0  # 0 = hidden above the screen, 1 = in the middle
enemy_menu_was_paused = False
ENEMY_TYPES = [("red", "Red", "Chases you down"), ("green", "Green", "Fast chaser"),
               ("blue", "Blue", "Shoots red lasers"), ("purple", "Purple", "Guarded by 4 minis"),
               ("orange", "Orange", "Fires a long laser"), ("yellow", "Yellow", "Flings a charged orb"),
               ("teal", "Teal", "Sneaks up and explodes"), ("pink", "Pink", "Zigzags in diagonally"),
               ("violet", "Violet", "Stands still and pulls you in")]

def enemy_menu_layout():
    """Panel, each enemy row with its three buttons, and the Close button, at the current slide position."""
    row_gap = 72  # Tight rows so every enemy fits on screen
    width, height = 760, 96 + len(ENEMY_TYPES) * row_gap + 76
    resting_y = HEIGHT // 2 - height // 2
    y = -height + (height + resting_y) * ease_out_back(min(1.0, enemy_menu_anim))
    panel = pygame.Rect(WIDTH // 2 - width // 2, y, width, height)
    rows = []
    for i, (kind, name, blurb) in enumerate(ENEMY_TYPES):
        row = pygame.Rect(panel.x + 24, panel.y + 96 + i * row_gap, width - 48, 64)
        buttons = {"add": pygame.Rect(row.right - 390, row.centery - 22, 110, 44),
                   "remove": pygame.Rect(row.right - 268, row.centery - 22, 120, 44),
                   "clear": pygame.Rect(row.right - 136, row.centery - 22, 124, 44)}
        rows.append((kind, name, blurb, row, buttons))
    close = pygame.Rect(panel.centerx - 90, panel.bottom - 64, 180, 48)
    return panel, rows, close

def sandbox_enemy_group(kind):
    return {"red": red_enemies, "green": green_enemies, "blue": blue_enemies, "purple": purple_enemies,
            "orange": orange_enemies, "yellow": yellow_enemies, "teal": teal_enemies, "pink": pink_enemies, "violet": violet_enemies}[kind]

def sandbox_add_enemy(kind):
    global max_red_enemies, max_green_enemies, max_blue_enemies, max_purple_enemies
    if kind == "orange":
        orange_enemies.append(new_orange_enemy(*get_safe_enemy_spawn()))
    elif kind == "yellow":
        yellow_enemies.append(new_yellow_enemy(*get_safe_enemy_spawn()))
    elif kind == "teal":
        teal_enemies.append(new_teal_enemy(*get_safe_enemy_spawn()))
    elif kind == "pink":
        pink_enemies.append(new_pink_enemy(*get_safe_enemy_spawn()))
    elif kind == "violet":
        violet_enemies.append(new_violet_enemy(*get_safe_enemy_spawn()))
    elif kind == "purple":
        spawn_purple()
        max_purple_enemies = len(purple_enemies)
    else:
        sandbox_enemy_group(kind).append(get_safe_enemy_spawn())
        if kind == "blue":
            blue_last_shot_times.append(0)
            max_blue_enemies = len(blue_enemies)
        elif kind == "green":
            max_green_enemies = len(green_enemies)
        else:
            max_red_enemies = len(red_enemies)

def sandbox_remove_enemy(kind, everything=False):
    """Remove one random enemy of this kind, or all of them."""
    global max_red_enemies, max_green_enemies, max_blue_enemies, max_purple_enemies
    group = sandbox_enemy_group(kind)
    if not group:
        return
    if kind in ("orange", "yellow", "teal", "pink", "violet"):
        if everything:
            group.clear()
        else:
            group.pop(random.randrange(len(group)))
        return
    if kind == "purple":
        if everything:
            purple_enemies.clear()
            purple_mini_circles.clear()
        else:
            remove_purple(random.randrange(len(purple_enemies)))
        max_purple_enemies = len(purple_enemies)
        return
    if everything:
        group.clear()
        if kind == "blue":
            blue_last_shot_times.clear()
    else:
        index = random.randrange(len(group))
        group.pop(index)
        if kind == "blue" and index < len(blue_last_shot_times):
            blue_last_shot_times.pop(index)
    if kind == "red":
        max_red_enemies = len(red_enemies)
    elif kind == "green":
        max_green_enemies = len(green_enemies)
    else:
        max_blue_enemies = len(blue_enemies)

def open_enemy_menu():
    global enemy_menu_open, enemy_menu_was_paused, game_paused
    enemy_menu_was_paused = game_paused
    enemy_menu_open = True
    game_paused = True

def close_enemy_menu():
    global enemy_menu_open, game_paused
    enemy_menu_open = False
    game_paused = enemy_menu_was_paused

def draw_enemy_menu():
    shade = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    shade.fill((0, 0, 0, int(150 * min(1.0, enemy_menu_anim))))
    screen.blit(shade, (0, 0))
    panel, rows, close = enemy_menu_layout()
    draw_panel(panel)
    title = get_bubble_text("Add Enemies", 56, (255, 240, 150), (255, 160, 40))
    screen.blit(title, title.get_rect(center=(panel.centerx, panel.y + 52)))
    orbs = {"red": red_orb, "green": green_orb, "blue": blue_orb, "purple": purple_orb, "orange": orange_orb, "yellow": yellow_orb, "teal": teal_orb, "pink": pink_orb, "violet": violet_orb}
    for kind, name, blurb, row, buttons in rows:
        draw_panel(row, radius=12)
        icon = pygame.transform.smoothscale(orbs[kind], (52, 52))
        screen.blit(icon, icon.get_rect(midleft=(row.x + 10, row.centery)))
        name_text = button_font.render(name, True, WHITE)
        screen.blit(name_text, (row.x + 72, row.y + 8))
        blurb_text = small_button_font.render(blurb, True, (190, 196, 205))
        screen.blit(blurb_text, (row.x + 72, row.y + 40))
        count_text = coin_font.render(f"x{len(sandbox_enemy_group(kind))}", True, (255, 222, 95))
        screen.blit(count_text, count_text.get_rect(midright=(buttons["add"].x - 18, row.centery)))
        for action, label, color in (("add", "Add 1", GREEN), ("remove", "Remove 1", BLUE), ("clear", "Remove All", DARK_RED)):
            draw_button(buttons[action], color)
            text = smaller_button_font.render(label, True, BLACK)
            screen.blit(text, text.get_rect(center=buttons[action].center))
    draw_button(close, BLUE)
    close_text = button_font.render("Close", True, BLACK)
    screen.blit(close_text, close_text.get_rect(center=close.center))

def handle_enemy_menu_event(event):
    if event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
        close_enemy_menu()
        return
    if event.type != pygame.MOUSEBUTTONDOWN or event.button != 1 or enemy_menu_anim < 0.9:
        return  # Ignore clicks until it has finished sliding in
    pos = pygame.mouse.get_pos()
    _, rows, close = enemy_menu_layout()
    if close.collidepoint(pos):
        close_enemy_menu()
        return
    for kind, _, _, _, buttons in rows:
        if buttons["add"].collidepoint(pos):
            sandbox_add_enemy(kind)
        elif buttons["remove"].collidepoint(pos):
            sandbox_remove_enemy(kind)
        elif buttons["clear"].collidepoint(pos):
            sandbox_remove_enemy(kind, everything=True)

# ---- Settings ----
settings_open = False
settings_confirm = None  # None, "data" or "account" while an "are you sure?" box is showing
SETTINGS_DISPLAY_BUTTON = pygame.Rect(WIDTH // 2 - 150, 250, 300, 60)
SETTINGS_DELETE_DATA_BUTTON = pygame.Rect(WIDTH // 2 - 150, 430, 300, 60)
SETTINGS_DELETE_ACCOUNT_BUTTON = pygame.Rect(WIDTH // 2 - 150, 510, 300, 60)
CONFIRM_YES_BUTTON = pygame.Rect(WIDTH // 2 - 220, 520, 200, 60)
CONFIRM_NO_BUTTON = pygame.Rect(WIDTH // 2 + 20, 520, 200, 60)

def draw_settings():
    """The standalone Settings screen (main menu and pause menu)."""
    title = get_bubble_text("SETTINGS", 76, (255, 240, 150), (255, 160, 40))
    screen.blit(title, (WIDTH // 2 - title.get_width() // 2, 8))
    draw_settings_content()
    draw_back_button()

def draw_settings_content():
    """Just the settings themselves, so the hub's Settings tab can reuse them."""
    draw_panel(pygame.Rect(WIDTH // 2 - 320, 180, 640, 170))
    display_label = coin_font.render("Display", True, WHITE)
    screen.blit(display_label, display_label.get_rect(center=(WIDTH // 2, 215)))
    fullscreen = bool(screen.get_flags() & pygame.FULLSCREEN)
    draw_button(SETTINGS_DISPLAY_BUTTON, BLUE)
    display_text = button_font.render("Fullscreen" if fullscreen else "Windowed", True, BLACK)
    screen.blit(display_text, display_text.get_rect(center=SETTINGS_DISPLAY_BUTTON.center))
    display_hint = small_button_font.render("Click to switch (or press F11 any time)", True, (205, 210, 216))
    screen.blit(display_hint, display_hint.get_rect(center=(WIDTH // 2, 330)))
    draw_panel(pygame.Rect(WIDTH // 2 - 320, 375, 640, 215))
    danger_label = coin_font.render("Danger Zone", True, (255, 130, 130))
    screen.blit(danger_label, danger_label.get_rect(center=(WIDTH // 2, 405)))
    for rect, label in ((SETTINGS_DELETE_DATA_BUTTON, "Delete Data"), (SETTINGS_DELETE_ACCOUNT_BUTTON, "Delete Account")):
        draw_button(rect, DARK_RED)
        text = button_font.render(label, True, BLACK)
        screen.blit(text, text.get_rect(center=rect.center))
    if settings_confirm:
        draw_settings_confirm()

def draw_settings_confirm():
    """The 'are you sure?' box over the Settings screen."""
    shade = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
    shade.fill((0, 0, 0, 170))
    screen.blit(shade, (0, 0))
    panel = pygame.Rect(WIDTH // 2 - 300, 300, 600, 280)
    draw_panel(panel)
    heading = font.render("Are you sure?", True, (255, 130, 130))
    screen.blit(heading, heading.get_rect(center=(WIDTH // 2, panel.y + 50)))
    if settings_confirm == "data":
        lines = ["This wipes this account's coins, skins,", "upgrades and abilities.", "The account itself stays."]
    else:
        lines = ["This deletes your account and everything in it,", "and sends you back to the login screen.", "This cannot be undone."]
    for i, line in enumerate(lines):
        text = small_button_font.render(line, True, WHITE)
        screen.blit(text, text.get_rect(center=(WIDTH // 2, panel.y + 110 + i * 30)))
    draw_button(CONFIRM_YES_BUTTON, DARK_RED)
    yes_text = button_font.render("Yes, delete", True, BLACK)
    screen.blit(yes_text, yes_text.get_rect(center=CONFIRM_YES_BUTTON.center))
    draw_button(CONFIRM_NO_BUTTON, BLUE)
    no_text = button_font.render("Cancel", True, BLACK)
    screen.blit(no_text, no_text.get_rect(center=CONFIRM_NO_BUTTON.center))

def handle_settings_event(event):
    """The standalone Settings screen: Back, then the settings themselves."""
    global settings_open, settings_from_pause, pause_menu_open, start_screen
    if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
        if pygame.Rect(20, 20, 100, 40).collidepoint(pygame.mouse.get_pos()) and not settings_confirm:
            settings_open = False
            if settings_from_pause:  # Opened from a game, so go back to the pause menu
                settings_from_pause = False
                pause_menu_open = True
            else:
                start_screen = True
            return
    handle_settings_content_event(event)

def handle_settings_content_event(event):
    global settings_open, settings_confirm, start_screen, current_account, login_screen_open
    global settings_from_pause, pause_menu_open, hub_open
    global login_message, login_message_ok, console_message, console_message_timer
    if event.type != pygame.MOUSEBUTTONDOWN or event.button != 1:
        return
    pos = pygame.mouse.get_pos()
    if settings_confirm:
        if CONFIRM_YES_BUTTON.collidepoint(pos):
            if settings_confirm == "data":
                apply_progress({})  # Back to a brand-new account's progress
                save_current_account()
                console_message, console_message_timer = "Account data deleted", 3.0
            else:
                if online_session is not None:
                    try:
                        cube_online.delete_account(online_session)
                    except (cube_online.OfflineError, cube_online.ServerError):
                        console_message, console_message_timer = "Couldn't delete the account - check your internet", 3.0
                        settings_confirm = None
                        return
                    globals()["online_session"] = None
                cube_accounts.forget_remembered(save_data)
                cube_accounts.delete_account(save_data, current_account)
                current_account = None
                apply_progress({})
                settings_open = False
                hub_open = False
                login_screen_open = True
                login_fields["username"], login_fields["password"] = "", ""
                login_message, login_message_ok = "Account deleted", False
            settings_confirm = None
        elif CONFIRM_NO_BUTTON.collidepoint(pos):
            settings_confirm = None
        return
    if SETTINGS_DISPLAY_BUTTON.collidepoint(pos):
        pygame.display.toggle_fullscreen()
    elif SETTINGS_DELETE_DATA_BUTTON.collidepoint(pos):
        settings_confirm = "data"
    elif SETTINGS_DELETE_ACCOUNT_BUTTON.collidepoint(pos):
        settings_confirm = "account"

def draw_account_bar():
    """Logged-in player's name, coins and best wave (top left) and the Log Out button (top right)."""
    if current_account is None:
        return
    name_text = coin_font.render(f"Player: {current_account}", True, WHITE)
    screen.blit(name_text, (20, 20))
    stats_text = small_button_font.render(f"Coins: {main_game_coins}    Best wave: {best_wave}", True, (205, 210, 216))
    screen.blit(stats_text, (20, 56))
    draw_button(LOGOUT_BUTTON, BLUE)
    logout_text = smaller_button_font.render("Log Out", True, BLACK)
    screen.blit(logout_text, logout_text.get_rect(center=LOGOUT_BUTTON.center))

def draw_scrollbar(viewport, scroll, max_scroll):
    if max_scroll <= 0:
        return
    track = pygame.Rect(WIDTH - 18, viewport.y + 10, 6, viewport.height - 20)
    pygame.draw.rect(screen, (40, 44, 50), track, border_radius=3)
    thumb_h = max(40, track.height * viewport.height / (viewport.height + max_scroll))
    thumb_y = track.y + (track.height - thumb_h) * min(1.0, max(0.0, scroll / max_scroll))
    pygame.draw.rect(screen, (215, 220, 228), (track.x, thumb_y, track.width, thumb_h), border_radius=3)

def draw_back_button():
    back = pygame.Rect(20, 20, 100, 40)
    draw_button(back, BLUE)
    text = button_font.render("Back", True, BLACK)
    screen.blit(text, text.get_rect(center=back.center))

def skin_face(skin, t):
    """What a skin's cube face looks like: its texture, the cycling rainbow color, or a flat color."""
    if skin == "rainbow":
        return rainbow_color_cycle(t, 2.0)
    if skin in SKIN_TEXTURES:
        return SKIN_TEXTURES[skin]
    return skin_colors.get(skin, WHITE)

def draw_skin_preview(card, skin, t, seed):
    """The real player cube in this skin, looking around, at the top of a card."""
    face = skin_face(skin, t)
    glow = SKIN_GLOWS.get(skin, face if isinstance(face, tuple) else WHITE)
    draw_player_cube(card.centerx - 42, card.y + 34, face, glow, t * 1.5 + seed, size=84)

# ---- Hub: one screen with tabs, opened by Play on the main menu ----
hub_open = False
hub_tab = "Play"
HUB_TABS = ["Play", "Shop", "Upgrades", "Abilities", "Locker", "Settings", "Main Menu"]
HUB_TAB_RECTS = {}
_tab_w, _tab_gap = 150, 8
_tabs_left = (WIDTH - (len(HUB_TABS) * _tab_w + (len(HUB_TABS) - 1) * _tab_gap)) // 2
for _i, _tab in enumerate(HUB_TABS):
    HUB_TAB_RECTS[_tab] = pygame.Rect(_tabs_left + _i * (_tab_w + _tab_gap), 118, _tab_w, 48)
HUB_VIEWPORT = pygame.Rect(0, 186, WIDTH, HEIGHT - 196)

SHOP_ICONS = {"gun": create_orb_sprite((120, 200, 255), 30, glow=8),
              "magnet": create_orb_sprite((255, 200, 60), 30, glow=8)}

def draw_shop_card(card, button, tag, icon, name, button_color, label):
    """One shop/locker card: type tag, icon, name and a button."""
    draw_panel(card, highlight=button_color == GREEN)
    tag_text = small_button_font.render(tag, True, (255, 220, 120))
    screen.blit(tag_text, (card.x + 12, card.y + 10))
    if icon is not None:
        draw_orb(icon, None, card.centerx, card.y + 76)
    name_text = coin_font.render(name, True, WHITE)
    screen.blit(name_text, name_text.get_rect(center=(card.centerx, card.y + 158)))
    draw_button(button, button_color)
    label_text = small_button_font.render(label, True, BLACK)
    screen.blit(label_text, label_text.get_rect(center=button.center))

# ---- Play tab: pick a mode, then press Play ----
GAME_MODES = [
    ("Waves", "Endless waves of enemies, one wave after another"),
    ("Barrier Shrink", "Survive three minutes while the map closes in"),
    ("Block Defence", "Stop the red enemies reaching your block"),
    ("Sandbox", "Add enemies and try everything out"),
    ("Tutorial", "Learn the controls step by step"),
]
selected_mode = "Waves"
PLAY_CENTER_X = min(WIDTH // 2, WIDTH - 650)  # Leaves room for the lobby panel
PLAY_BUTTON = pygame.Rect(PLAY_CENTER_X - 160, HUB_VIEWPORT.y + 470, 320, 72)

def map_button_rects():
    width, gap = 170, 16
    left = PLAY_CENTER_X - (len(MAP_NAMES) * width + (len(MAP_NAMES) - 1) * gap) // 2
    return [(name, pygame.Rect(left + i * (width + gap), HUB_VIEWPORT.y + 385, width, 50))
            for i, name in enumerate(MAP_NAMES)]

def mode_row_rects():
    return [(name, pygame.Rect(PLAY_CENTER_X - 280, HUB_VIEWPORT.y + 20 + i * 62, 560, 54))
            for i, (name, _) in enumerate(GAME_MODES)]

def draw_play_tab():
    for (name, rect), (_, description) in zip(mode_row_rects(), GAME_MODES):
        chosen = name == selected_mode
        solo_only = play_multiplayer and name in MULTIPLAYER_SOLO_MODES
        draw_button(rect, GREY_BUTTON if solo_only else GREEN if chosen else BLUE)
        label = button_font.render(name, True, BLACK)
        screen.blit(label, label.get_rect(midleft=(rect.x + 22, rect.centery)))
        if chosen or solo_only:
            tick = smaller_button_font.render("solo only" if solo_only else "selected", True, (40, 90, 50) if chosen else (40, 40, 40))
            screen.blit(tick, tick.get_rect(midright=(rect.right - 18, rect.centery)))
    description = next(text for name, text in GAME_MODES if name == selected_mode)
    info = coin_font.render(description, True, (210, 215, 222))
    screen.blit(info, info.get_rect(center=(PLAY_CENTER_X, HUB_VIEWPORT.y + 350)))
    # Map picker: works for every mode
    rects = map_button_rects()
    map_label = coin_font.render("Map:", True, WHITE)
    screen.blit(map_label, map_label.get_rect(midright=(rects[0][1].x - 14, rects[0][1].centery)))
    for name, rect in rects:
        draw_button(rect, GREEN if name == selected_map else BLUE)
        swatch = pygame.transform.smoothscale(MAP_TEXTURES[name], (34, 34))
        swatch_rect = swatch.get_rect(midleft=(rect.x + 10, rect.centery))
        screen.blit(swatch, swatch_rect)
        pygame.draw.rect(screen, (40, 40, 40), swatch_rect, 2, border_radius=4)
        text = smaller_button_font.render(name, True, BLACK)
        screen.blit(text, text.get_rect(midleft=(swatch_rect.right + 12, rect.centery)))
    waiting = multiplayer_guest() or (play_multiplayer and not net.lobby)
    draw_button(PLAY_BUTTON, GREY_BUTTON if waiting else GREEN)
    if multiplayer_guest():
        play_label = small_button_font.render("Waiting for the host", True, BLACK)
    else:
        play_label = font.render("PLAY", True, BLACK)
    screen.blit(play_label, play_label.get_rect(center=PLAY_BUTTON.center))
    draw_lobby_panel()

sandbox_entry_coins = 0  # Your real coins when the Sandbox started; the Sandbox can't change them
sandbox_snapshot = None  # Where every enemy was when the Sandbox last switched into play mode

def snapshot_sandbox():
    """Remember every enemy's position (and the purples' minis) so Retry can put them back."""
    return {"red": [list(e) for e in red_enemies], "green": [list(e) for e in green_enemies],
            "blue": [list(e) for e in blue_enemies], "purple": [list(e) for e in purple_enemies],
            "minis": [[list(m) for m in minis] for minis in purple_mini_circles],
            "orange": [(e["x"], e["y"]) for e in orange_enemies],
            "yellow": [(e["x"], e["y"]) for e in yellow_enemies],
            "teal": [(e["x"], e["y"]) for e in teal_enemies],
            "pink": [(e["x"], e["y"]) for e in pink_enemies],
            "violet": [(e["x"], e["y"]) for e in violet_enemies]}

def retry_sandbox():
    """Retry after dying in the Sandbox: straight back into play mode with the enemies you had placed."""
    global shooting_range_editor_mode, shooting_range_play_mode
    global max_red_enemies, max_green_enemies, max_blue_enemies, max_purple_enemies
    reset_game(shooting_range=True)
    if sandbox_snapshot is None:
        return  # Nothing saved yet, so it's just a fresh Sandbox
    red_enemies[:] = [list(e) for e in sandbox_snapshot["red"]]
    green_enemies[:] = [list(e) for e in sandbox_snapshot["green"]]
    blue_enemies[:] = [list(e) for e in sandbox_snapshot["blue"]]
    blue_last_shot_times[:] = [0] * len(blue_enemies)
    purple_enemies[:] = [list(e) for e in sandbox_snapshot["purple"]]
    purple_mini_circles[:] = [[list(m) for m in minis] for minis in sandbox_snapshot["minis"]]
    orange_enemies[:] = [new_orange_enemy(x, y) for x, y in sandbox_snapshot["orange"]]
    yellow_enemies[:] = [new_yellow_enemy(x, y) for x, y in sandbox_snapshot["yellow"]]
    teal_enemies[:] = [new_teal_enemy(x, y) for x, y in sandbox_snapshot.get("teal", [])]
    pink_enemies[:] = [new_pink_enemy(x, y) for x, y in sandbox_snapshot.get("pink", [])]
    violet_enemies[:] = [new_violet_enemy(x, y) for x, y in sandbox_snapshot.get("violet", [])]
    max_red_enemies, max_green_enemies = len(red_enemies), len(green_enemies)
    max_blue_enemies, max_purple_enemies = len(blue_enemies), len(purple_enemies)
    shooting_range_editor_mode = False
    shooting_range_play_mode = True

# ---- Multiplayer lobby (right side of the Play tab) ----
MULTIPLAYER_SOLO_MODES = ("Sandbox", "Tutorial")  # These stay single-player
net = cube_net.Net()
play_multiplayer = False      # The Solo / Multiplayer switch
multiplayer_match = False     # In a match that started from a lobby
join_code_text = ""
join_code_focused = False
net_sent_settings = None      # (mode, map) the host last told the lobby

# Other players in the match: where they are (smoothed between updates), their skin, and their shots
remote_players = {}           # name -> {"x", "y", "a", "skin", "dead", "from_x", "from_y", "to_x", "to_y", "since"}
remote_bullets = []           # Other players' shots, flying on this screen
NET_SEND_EVERY = 0.05         # 20 updates a second
net_send_timer = 0.0

def reset_remote_players():
    remote_players.clear()
    remote_bullets.clear()

def in_multiplayer_game():
    return multiplayer_match and not (start_screen or hub_open or login_screen_open)

net_shot_outbox = []  # Our shots fired since the last update

def collect_new_shots():
    """Note every shot we've fired that the others haven't heard about. Runs before shots can hit anything,
    so even a point-blank hit still reaches the other games."""
    if not multiplayer_match:
        return
    for bullet in bullets:
        if not bullet.get("sent"):
            bullet["sent"] = True
            net_shot_outbox.append([round(bullet["x"], 1), round(bullet["y"], 1), round(bullet["dx"], 2), round(bullet["dy"], 2)])

def send_player_state(dt):
    """Tell the others where we are, where we aim, our skin, and any shots fired since the last update."""
    global net_send_timer
    net_send_timer -= dt
    if net_send_timer > 0:
        return
    net_send_timer = NET_SEND_EVERY
    collect_new_shots()
    shots = net_shot_outbox[:]
    net_shot_outbox.clear()
    net.relay({"k": "p", "x": round(player_x, 1), "y": round(player_y, 1), "a": round(last_rot_angle, 3),
               "s": current_skin, "d": bool(game_over), "b": shots})

def receive_player_state(name, data):
    now = time.monotonic()
    player = remote_players.get(name)
    x, y = float(data.get("x", 0)), float(data.get("y", 0))
    if player is None:
        player = remote_players[name] = {"x": x, "y": y, "from_x": x, "from_y": y}
    else:
        player["from_x"], player["from_y"] = player["x"], player["y"]  # Glide on from wherever it's drawn now
    player.update({"to_x": x, "to_y": y, "since": now, "a": float(data.get("a", 0)),
                   "skin": str(data.get("s", "white")), "dead": bool(data.get("d"))})
    for shot in data.get("b", [])[:20]:
        bx, by, dx, dy = (float(v) for v in shot[:4])
        # Already "sent" so it isn't passed on again; its owner is who fired it
        bullets.append({"x": bx, "y": by, "dx": dx, "dy": dy, "sent": True, "owner": name, "age": 0})

def update_remote_players():
    """Smooth each other player toward their latest position, and move their shots along."""
    now = time.monotonic()
    names = set(net.lobby["players"]) if net.lobby else set()
    for name in list(remote_players):
        if name not in names:
            del remote_players[name]  # Left the lobby
            continue
        player = remote_players[name]
        k = min(1.0, (now - player["since"]) / (NET_SEND_EVERY * 1.2))
        player["x"] = player["from_x"] + (player["to_x"] - player["from_x"]) * k
        player["y"] = player["from_y"] + (player["to_y"] - player["from_y"]) * k

def draw_remote_players():
    for name, player in remote_players.items():
        if player.get("dead"):
            continue
        skin = player.get("skin", "white")
        if skin == "rainbow":
            color = rainbow_color_cycle(pygame.time.get_ticks() / 1000.0, 2.0)
        else:
            color = skin_colors.get(skin, WHITE)
        face = SKIN_TEXTURES.get(skin, color)
        sx, sy = player["x"] - camera_x, player["y"] - camera_y
        if not on_screen(sx + player_size / 2, sy + player_size / 2, 120):
            continue
        draw_player_cube(sx, sy, face, SKIN_GLOWS.get(skin, color), player.get("a", 0))
        tag = smaller_button_font.render(name, True, WHITE)
        box = tag.get_rect(midbottom=(sx + player_size / 2, sy - 10)).inflate(12, 4)
        pygame.draw.rect(screen, (20, 24, 32), box, border_radius=6)
        screen.blit(tag, tag.get_rect(center=box.center))

# ---- The shared world: the host sends it, everyone else shows it ----
NET_WORLD_EVERY = 0.1          # The host sends the whole world 10 times a second
net_world_timer = 0.0
net_events = []                # Host: things that happened since the last send (kills, finished waves)
recent_local_kills = []        # Not the host: enemies we just shot, so the next world update doesn't bring them back
MULTIPLAYER_REPAIR_REQUEST = "repair"

def net_role():
    """ "host" or "guest" during a multiplayer match, else None."""
    if not multiplayer_match:
        return None
    return "host" if net.is_host else "guest"

def json_safe(value):
    if isinstance(value, (set, tuple)):
        return list(value)
    raise TypeError("can't send %r" % type(value))

def pack_world():
    world = {
        "wave": wave, "timer": round(game_timer, 2),
        "red": red_enemies, "green": green_enemies, "blue": blue_enemies,
        "purple": purple_enemies, "minis": purple_mini_circles,
        "orange": orange_enemies, "yellow": yellow_enemies, "teal": teal_enemies,
        "pink": pink_enemies, "violet": violet_enemies,
        "boss": active_boss, "shots": blue_bullets,
        "storm": [storm_survival_map_width, storm_survival_map_height, globals().get("storm_survival_won", False)],
        "block": [globals().get("block_health", 0), globals().get("block_defence_points", 0)],
        "events": net_events,
    }
    raw = json.dumps(world, default=json_safe, separators=(",", ":")).encode("utf-8")
    return base64.b64encode(zlib.compress(raw, 6)).decode("ascii")

def send_world(dt):
    global net_world_timer
    net_world_timer -= dt
    if net_world_timer > 0:
        return
    net_world_timer = NET_WORLD_EVERY
    net.relay({"k": "w", "z": pack_world()})
    net_events.clear()

def recently_shot(kind, x, y):
    now = time.monotonic()
    return any(k == kind and now - when < 0.6 and abs(x - kx) < 40 and abs(y - ky) < 40
               for k, kx, ky, when in recent_local_kills)

def apply_world(packed):
    """Not the host: replace this game's enemies, boss and enemy shots with the host's."""
    global wave, game_timer, active_boss, storm_survival_map_width, storm_survival_map_height, storm_survival_won
    global block_health, block_defence_points
    world = json.loads(zlib.decompress(base64.b64decode(packed)))
    now = time.monotonic()
    recent_local_kills[:] = [k for k in recent_local_kills if now - k[3] < 0.6]
    keep = lambda kind, items, pos: [e for e in items if not recently_shot(kind, *pos(e))]
    red_enemies[:] = keep("red", world["red"], lambda e: e)
    green_enemies[:] = keep("green", world["green"], lambda e: e)
    blue_enemies[:] = keep("blue", world["blue"], lambda e: e)
    blue_last_shot_times[:] = [pygame.time.get_ticks() / 1000] * len(blue_enemies)  # Their shots come from the host
    pairs = [(p, m) for p, m in zip(world["purple"], world["minis"]) if not recently_shot("purple", *p)]
    purple_enemies[:] = [p for p, _ in pairs]
    purple_mini_circles[:] = [m for _, m in pairs]
    for kind, group in (("orange", orange_enemies), ("yellow", yellow_enemies), ("teal", teal_enemies),
                        ("pink", pink_enemies), ("violet", violet_enemies)):
        group[:] = keep(kind, world[kind], lambda e: (e["x"], e["y"]))
    active_boss = world["boss"]
    blue_bullets[:] = world["shots"]
    wave, game_timer = world["wave"], world["timer"]
    storm_survival_map_width, storm_survival_map_height, storm_survival_won = world["storm"]
    block_health, block_defence_points = world["block"]
    for event in world["events"]:
        apply_world_event(event)

def apply_world_event(event):
    """Not the host: something happened in the host's game."""
    global coin_count, main_game_coins, best_wave, wave_completion_message, wave_completion_timer, block_defence_coins
    kind = event[0]
    if kind == "kill":
        _, x, y, enemy = event
        if not in_shooting_range:
            drop_coin(x, y)  # Everyone gets their own coin from every kill
        if not any(k == enemy and abs(x - player_size / 2 - kx) < 40 and abs(y - player_size / 2 - ky) < 40
                   for k, kx, ky, _ in recent_local_kills):
            spawn_death_effect(x, y, enemy)  # We didn't already see it burst
            sounds.play("enemy_death")
    elif kind == "wave":
        _, reward, boss_wave, number = event
        wave_completion_message = "Boss Wave Completed!" if boss_wave else f"Wave {number} Complete!"
        wave_completion_timer = wave_completion_duration
        sounds.play("boss_wave_complete" if boss_wave else "wave_complete")
        best_wave = max(best_wave, number)
        coin_count += reward
        main_game_coins = coin_count

def receive_world_message(name, data):
    """Handle a game message from another player (not a position update)."""
    global block_defence_points, block_health
    kind = data.get("k")
    if kind == "w" and net_role() == "guest" and name == net.lobby.get("host"):
        apply_world(data["z"])
    elif kind == MULTIPLAYER_REPAIR_REQUEST and net_role() == "host" and in_block_defence:
        index = int(data.get("i", -1))
        if 0 <= index < len(BLOCK_REPAIRS):
            health, cost = BLOCK_REPAIRS[index]
            if block_defence_points >= cost and block_health < BLOCK_MAX_HEALTH:  # Points are shared
                block_defence_points -= cost
                block_health = min(BLOCK_MAX_HEALTH, block_health + health)

def lobby_panel():
    left = PLAY_CENTER_X + 300
    return pygame.Rect(left, HUB_VIEWPORT.y + 20, WIDTH - 30 - left, 470)

def lobby_layout():
    panel = lobby_panel()
    half = (panel.width - 36) // 2
    return {
        "solo": pygame.Rect(panel.x + 12, panel.y + 12, half, 46),
        "multi": pygame.Rect(panel.x + 24 + half, panel.y + 12, half, 46),
        "code_box": pygame.Rect(panel.x + 12, panel.bottom - 60, panel.width - 136, 48),
        "join": pygame.Rect(panel.right - 112, panel.bottom - 60, 100, 48),
    }

def set_play_multiplayer(on):
    """Flip the Solo / Multiplayer switch: Multiplayer connects and opens a lobby with a code."""
    global play_multiplayer, net_sent_settings, selected_mode, join_code_focused
    play_multiplayer = on
    join_code_focused = False
    net_sent_settings = None
    if not on:
        if net.lobby:
            net.leave_lobby()
        return
    if selected_mode in MULTIPLAYER_SOLO_MODES:
        selected_mode = "Waves"
    if online_session is None:
        net.error = "Log in to an online account to play multiplayer"
        return
    if net.status == "offline":
        try:
            net.connect(online_session.token())
        except (cube_online.OfflineError, cube_online.ServerError):
            net.error = "Can't reach the server - check your internet"
    elif net.status == "online" and not net.lobby:
        net.create_lobby()

def multiplayer_guest():
    """In someone else's lobby: the host picks the mode and map and presses Play."""
    return play_multiplayer and net.lobby is not None and not net.is_host

def update_multiplayer():
    """Every frame: handle what the server sent, keep the lobby's mode/map in sync."""
    global selected_mode, selected_map, net_sent_settings, multiplayer_match
    for msg in net.poll():
        kind = msg.get("t")
        if kind == "welcome" and play_multiplayer and not net.lobby:
            net.create_lobby()  # Pressing Multiplayer opens your own lobby straight away
        elif kind == "relay":
            data = msg.get("d")
            if isinstance(data, dict) and multiplayer_match:
                try:
                    if data.get("k") == "p":
                        receive_player_state(str(msg.get("from")), data)
                    else:
                        receive_world_message(str(msg.get("from")), data)
                except (TypeError, ValueError, KeyError, AttributeError, zlib.error) as err:
                    if os.environ.get("CUBE_SHOOTER_NETDEBUG"):
                        print("bad multiplayer update:", repr(err), flush=True)
        elif kind == "start":
            reset_remote_players()
            net_shot_outbox.clear()
            net_events.clear()
            recent_local_kills.clear()
            selected_mode = msg.get("mode", selected_mode)
            if msg.get("map") in MAP_NAMES:
                selected_map = msg["map"]
            start_selected_mode()
            multiplayer_match = True
        elif kind in ("end", "disconnected"):
            if multiplayer_match and not (start_screen or hub_open):
                multiplayer_match = False
                exit_to_main_menu()  # The match is over (or the host left): back to the lobby
                globals().update(start_screen=False, hub_open=True, hub_tab="Play")
            multiplayer_match = False
            reset_remote_players()
    if in_multiplayer_game():
        frame_dt = globals().get("dt", 1 / 60)
        globals().update(game_paused=False, pause_countdown=0.0)  # The world keeps going for everyone
        send_player_state(frame_dt)
        if net_role() == "host":
            send_world(frame_dt)
        update_remote_players()
    lobby = net.lobby
    if not play_multiplayer or lobby is None:
        return
    if net.is_host:
        wanted = (selected_mode, selected_map)
        if wanted != net_sent_settings and not lobby.get("started"):
            net.send_settings(*wanted)
            net_sent_settings = wanted
    else:
        if lobby.get("mode") in dict(GAME_MODES):
            selected_mode = lobby["mode"]
        if lobby.get("map") in MAP_NAMES:
            selected_map = lobby["map"]

def draw_lobby_panel():
    panel = lobby_panel()
    draw_panel(panel)
    layout = lobby_layout()
    for key, label, chosen in (("solo", "Solo", not play_multiplayer), ("multi", "Multiplayer", play_multiplayer)):
        draw_button(layout[key], GREEN if chosen else BLUE)
        text = small_button_font.render(label, True, BLACK)
        screen.blit(text, text.get_rect(center=layout[key].center))
    x, y = panel.x + 20, panel.y + 80
    grey = (170, 175, 182)
    if not play_multiplayer:
        for i, line in enumerate(("Playing on your own.", "Switch to Multiplayer to get a", "code and play with up to 3 friends.")):
            text = small_button_font.render(line, True, grey)
            screen.blit(text, (x, y + i * 30))
        return
    if net.error and not net.lobby:
        for i, line in enumerate(wrap_text(net.error, small_button_font, panel.width - 40)):
            text = small_button_font.render(line, True, (255, 120, 110))
            screen.blit(text, (x, y + i * 28))
        hint = smaller_button_font.render("Click Multiplayer to try again", True, grey)
        screen.blit(hint, (x, y + 90))
    elif net.status != "online" or not net.lobby:
        dots = "." * (1 + pygame.time.get_ticks() // 400 % 3)
        text = small_button_font.render(("Waking up the server" if net.waking_up else "Connecting") + dots, True, grey)
        screen.blit(text, (x, y))
        if net.waking_up:
            for i, line in enumerate(("The server sleeps when nobody is", "playing. This can take up to a minute.")):
                hint = smaller_button_font.render(line, True, (140, 145, 152))
                screen.blit(hint, (x, y + 36 + i * 24))
    else:
        lobby = net.lobby
        label = small_button_font.render("Lobby code:", True, grey)
        screen.blit(label, (x, y))
        code = get_bubble_text(lobby["code"], 64, (255, 235, 120), (255, 170, 40), outline=6)
        screen.blit(code, code.get_rect(midtop=(panel.centerx, y + 26)))
        row_y = y + 112
        heading = small_button_font.render(f"Players ({len(lobby['players'])}/4)", True, WHITE)
        screen.blit(heading, (x, row_y))
        for i in range(4):
            row = pygame.Rect(x - 6, row_y + 32 + i * 40, panel.width - 28, 34)
            pygame.draw.rect(screen, (34, 38, 48), row, border_radius=8)
            if i < len(lobby["players"]):
                name = lobby["players"][i]
                you = " (you)" if name == net.name else ""
                text = small_button_font.render(name + you, True, WHITE)
                screen.blit(text, text.get_rect(midleft=(row.x + 12, row.centery)))
                if name == lobby["host"]:
                    tag = smaller_button_font.render("HOST", True, (255, 210, 80))
                    screen.blit(tag, tag.get_rect(midright=(row.right - 12, row.centery)))
            else:
                text = smaller_button_font.render("empty", True, (110, 115, 125))
                screen.blit(text, text.get_rect(midleft=(row.x + 12, row.centery)))
        if net.error:
            err = smaller_button_font.render(net.error, True, (255, 120, 110))
            screen.blit(err, (x, layout["code_box"].y - 28))
    if net.status == "online":
        box = layout["code_box"]
        pygame.draw.rect(screen, WHITE, box, border_radius=8)
        pygame.draw.rect(screen, (255, 200, 60) if join_code_focused else (40, 40, 40), box, 3 if join_code_focused else 2, border_radius=8)
        shown = join_code_text or ("" if join_code_focused else "Join a code")
        text = (button_font if join_code_text else small_button_font).render(shown, True, BLACK if join_code_text else (140, 140, 140))
        screen.blit(text, text.get_rect(midleft=(box.x + 12, box.centery)))
        draw_button(layout["join"], GREEN if len(join_code_text) == 4 else BLUE)
        join = small_button_font.render("Join", True, BLACK)
        screen.blit(join, join.get_rect(center=layout["join"].center))

def wrap_text(text, text_font, width):
    lines, line = [], ""
    for word in text.split():
        trial = (line + " " + word).strip()
        if text_font.size(trial)[0] > width and line:
            lines.append(line)
            line = word
        else:
            line = trial
    return lines + ([line] if line else [])

def handle_lobby_click(pos):
    """True if the click was on the lobby panel."""
    global join_code_focused
    layout = lobby_layout()
    if layout["solo"].collidepoint(pos):
        set_play_multiplayer(False)
    elif layout["multi"].collidepoint(pos):
        set_play_multiplayer(True)
    elif play_multiplayer and net.status == "online" and layout["code_box"].collidepoint(pos):
        join_code_focused = True
    elif play_multiplayer and net.status == "online" and layout["join"].collidepoint(pos):
        submit_join_code()
    else:
        join_code_focused = False
        return lobby_panel().collidepoint(pos)
    return True

def submit_join_code():
    global join_code_text, join_code_focused, net_sent_settings
    if len(join_code_text) == 4:
        net.join_lobby(join_code_text)
        net_sent_settings = None
        join_code_text, join_code_focused = "", False

def handle_lobby_key(event):
    """Typing a join code. True if the key was used."""
    global join_code_text
    if not (play_multiplayer and join_code_focused):
        return False
    if event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
        submit_join_code()
    elif event.key == pygame.K_BACKSPACE:
        join_code_text = join_code_text[:-1]
    elif event.unicode.isdigit() and len(join_code_text) < 4:
        join_code_text += event.unicode
    return True

def start_selected_mode():
    """Leave the hub and start whichever mode is selected."""
    global hub_open, start_screen, sandbox_snapshot
    hub_open = False
    start_screen = False
    if selected_mode == "Barrier Shrink":
        reset_game(storm_survival=True)
    elif selected_mode == "Block Defence":
        if hasattr(reset_game, "block_health_initialized"):
            delattr(reset_game, "block_health_initialized")
        reset_game(block_defence=True)
    elif selected_mode == "Sandbox":
        sandbox_snapshot = None  # A new Sandbox session starts with nothing saved
        reset_game(shooting_range=True)
    elif selected_mode == "Tutorial":
        reset_game(tutorial=True)
    else:
        reset_game()

def handle_play_tab_click(pos):
    global selected_mode, selected_map
    if handle_lobby_click(pos):
        return
    if multiplayer_guest():
        return  # The host chooses and starts
    for name, rect in map_button_rects():
        if rect.collidepoint(pos):
            selected_map = name
            return
    for name, rect in mode_row_rects():
        if rect.collidepoint(pos):
            if not (play_multiplayer and name in MULTIPLAYER_SOLO_MODES):
                selected_mode = name
            return
    if PLAY_BUTTON.collidepoint(pos):
        if play_multiplayer and net.lobby:
            net.send_settings(selected_mode, selected_map)  # Make sure the lobby has the latest pick first
            net.start_match()  # Everyone in the lobby starts together
        elif not play_multiplayer:
            start_selected_mode()

# ---- Shop tab: four daily skins ----
DAILY_VIEWPORT = pygame.Rect(0, 270, WIDTH, 300)

def daily_offers():
    """Today's shop skins - the same for everyone, new at midnight."""
    return cube_accounts.daily_items(DAILY_SKIN_POOL, seed=cube_accounts.daily_seed(save_data))

def skin_price(skin):
    return SKIN_PRICES.get(skin, 800)

def draw_shop_tab():
    subtitle = get_bubble_text("Daily Skins", 44, (255, 250, 200), (255, 200, 60), outline=6)
    screen.blit(subtitle, subtitle.get_rect(center=(WIDTH // 2, HUB_VIEWPORT.y + 20)))
    left = cube_accounts.seconds_until_midnight()
    countdown = coin_font.render(f"New skins in {left // 3600}h {left % 3600 // 60:02d}m", True, (205, 210, 216))
    screen.blit(countdown, countdown.get_rect(center=(WIDTH // 2, HUB_VIEWPORT.y + 68)))
    t = pygame.time.get_ticks() / 1000
    for i, skin in enumerate(daily_offers()):
        card, button = card_rects(i, DAILY_VIEWPORT, 0)
        owned = owned_skins.get(skin, False)
        equipped = skin == current_skin
        price = skin_price(skin)
        if equipped:
            button_color, label = GREEN, "Equipped"
        elif owned:
            button_color, label = BLUE, "Equip"
        elif main_game_coins >= price:
            button_color, label = BLUE, f"Buy - {price}"
        else:
            button_color, label = DARK_RED, f"Need {price}"
        draw_shop_card(card, button, "SKIN", None, skin.capitalize(), button_color, label)
        draw_skin_preview(card, skin, t, i)  # On top of the card, where the icon would go

def handle_shop_tab_click(pos):
    global main_game_coins, coin_count, current_skin, console_message, console_message_timer
    for i, skin in enumerate(daily_offers()):
        _, button = card_rects(i, DAILY_VIEWPORT, 0)
        if not button.collidepoint(pos):
            continue
        if owned_skins.get(skin):
            current_skin = skin  # Already bought, so this equips it
            return
        price = skin_price(skin)
        if main_game_coins >= price:
            main_game_coins -= price
            coin_count = main_game_coins
            owned_skins[skin] = True
            current_skin = skin
            console_message, console_message_timer = f"Bought {skin.capitalize()}!", 2.5
        return

# ---- Upgrades tab: gun and magnet levels ----
shop_upgrade_scroll = 0.0
shop_upgrade_scroll_target = 0.0
SHOP_UPGRADE_VIEWPORT = pygame.Rect(0, 186, WIDTH, HEIGHT - 196)
SHOP_UPGRADES = [
    {"tag": "GUN", "name": "Gun I", "flag": "has_gun_upgrade_1", "price": 1000, "needs": None, "needs_name": "", "icon": "gun"},
    {"tag": "GUN", "name": "Gun II", "flag": "has_gun_upgrade_2", "price": 2000, "needs": "has_gun_upgrade_1", "needs_name": "Gun I", "icon": "gun"},
    {"tag": "GUN", "name": "Gun III", "flag": "has_gun_upgrade_3", "price": 4000, "needs": "has_gun_upgrade_2", "needs_name": "Gun II", "icon": "gun"},
    {"tag": "GUN", "name": "Gun IV", "flag": "has_gun_upgrade_4", "price": 8000, "needs": "has_gun_upgrade_3", "needs_name": "Gun III", "icon": "gun"},
    {"tag": "GUN", "name": "Gun V", "flag": "has_gun_upgrade_5", "price": 16000, "needs": "has_gun_upgrade_4", "needs_name": "Gun IV", "icon": "gun"},
    {"tag": "MAGNET", "name": "Magnet I", "flag": "has_magnet_1", "price": 750, "needs": None, "needs_name": "", "icon": "magnet"},
    {"tag": "MAGNET", "name": "Magnet II", "flag": "has_magnet_2", "price": 1500, "needs": "has_magnet_1", "needs_name": "Magnet I", "icon": "magnet"},
    {"tag": "MAGNET", "name": "Magnet III", "flag": "has_magnet_3", "price": 3000, "needs": "has_magnet_2", "needs_name": "Magnet II", "icon": "magnet"},
    {"tag": "MAGNET", "name": "Magnet IV", "flag": "has_magnet_4", "price": 6000, "needs": "has_magnet_3", "needs_name": "Magnet III", "icon": "magnet"},
    {"tag": "MAGNET", "name": "Magnet V", "flag": "has_magnet_5", "price": 12000, "needs": "has_magnet_4", "needs_name": "Magnet IV", "icon": "magnet"},
]

def draw_upgrades_tab():
    global shop_upgrade_scroll
    shop_upgrade_scroll += (shop_upgrade_scroll_target - shop_upgrade_scroll) * 0.25
    screen.set_clip(SHOP_UPGRADE_VIEWPORT)
    for i, item in enumerate(SHOP_UPGRADES):
        card, button = card_rects(i, SHOP_UPGRADE_VIEWPORT, shop_upgrade_scroll)
        if card.bottom < SHOP_UPGRADE_VIEWPORT.top or card.top > SHOP_UPGRADE_VIEWPORT.bottom:
            continue
        owned = globals()[item["flag"]]
        locked = item["needs"] is not None and not globals()[item["needs"]]
        if owned:
            button_color, label = GREEN, "Owned"
        elif locked:
            button_color, label = DARK_RED, f"Needs {item['needs_name']}"
        elif main_game_coins >= item["price"]:
            button_color, label = BLUE, f"Buy - {item['price']}"
        else:
            button_color, label = DARK_RED, f"Need {item['price']}"
        draw_shop_card(card, button, item["tag"], SHOP_ICONS[item["icon"]], item["name"], button_color, label)
    screen.set_clip(None)
    draw_scrollbar(SHOP_UPGRADE_VIEWPORT, shop_upgrade_scroll, max_card_scroll(len(SHOP_UPGRADES), SHOP_UPGRADE_VIEWPORT))

def buy_shop_upgrade(item):
    global main_game_coins, coin_count, shot_delay, console_message, console_message_timer
    if globals()[item["flag"]] or main_game_coins < item["price"]:
        return
    if item["needs"] is not None and not globals()[item["needs"]]:
        return  # Earlier level not bought yet
    main_game_coins -= item["price"]
    coin_count = main_game_coins
    globals()[item["flag"]] = True
    if item["tag"] == "GUN":
        shot_delay = GUN_SHOT_DELAYS[gun_level()]
    console_message, console_message_timer = f"Bought {item['name']}!", 2.5
    sounds.play("buy")

def handle_upgrades_tab_click(pos):
    if not SHOP_UPGRADE_VIEWPORT.collidepoint(pos):
        return
    for i, item in enumerate(SHOP_UPGRADES):
        _, button = card_rects(i, SHOP_UPGRADE_VIEWPORT, shop_upgrade_scroll)
        if button.collidepoint(pos):
            buy_shop_upgrade(item)
            return

# ---- Abilities tab: buy them here, and equip the ones you own ----
ability_scroll = 0.0
ability_scroll_target = 0.0

def draw_abilities_tab():
    global ability_scroll
    ability_scroll += (ability_scroll_target - ability_scroll) * 0.25
    screen.set_clip(HUB_VIEWPORT)
    for i, (key, name, _, price) in enumerate(ABILITIES):
        card, button = card_rects(i, HUB_VIEWPORT, ability_scroll)
        if card.bottom < HUB_VIEWPORT.top or card.top > HUB_VIEWPORT.bottom:
            continue
        owned = globals()["has_" + key]
        if equipped_ability == key:
            button_color, label = GREEN, "Equipped"
        elif owned:
            button_color, label = BLUE, "Equip"
        elif main_game_coins >= price:
            button_color, label = BLUE, f"Buy - {price}"
        else:
            button_color, label = DARK_RED, f"Need {price}"
        draw_shop_card(card, button, "ABILITY", ABILITY_ICONS[key], name, button_color, label)
    screen.set_clip(None)
    draw_scrollbar(HUB_VIEWPORT, ability_scroll, max_card_scroll(len(ABILITIES), HUB_VIEWPORT))

def handle_abilities_tab_click(pos):
    global main_game_coins, coin_count, equipped_ability, console_message, console_message_timer
    if not HUB_VIEWPORT.collidepoint(pos):
        return
    for i, (key, name, _, price) in enumerate(ABILITIES):
        _, button = card_rects(i, HUB_VIEWPORT, ability_scroll)
        if not button.collidepoint(pos):
            continue
        if globals()["has_" + key]:
            equipped_ability = key  # Already bought, so this equips it
            return
        if main_game_coins >= price:
            main_game_coins -= price
            coin_count = main_game_coins
            globals()["has_" + key] = True
            equipped_ability = key
            console_message, console_message_timer = f"Bought {name}!", 2.5
        return

# ---- Locker tab: what you own, and equipping it ----
locker_scroll = 0.0
locker_scroll_target = 0.0
LOCKER_VIEWPORT = pygame.Rect(0, 196, WIDTH, HEIGHT - 206)

def locker_items():
    """The skins you own. Abilities have their own tab, where you buy and equip them."""
    return [skin for skin in shop_skins if owned_skins.get(skin)]

def draw_locker_tab():
    global locker_scroll
    items = locker_items()
    locker_scroll += (locker_scroll_target - locker_scroll) * 0.25
    if not items:
        empty = coin_font.render("No skins yet - buy some in the Shop!", True, (205, 210, 216))
        screen.blit(empty, empty.get_rect(center=(WIDTH // 2, LOCKER_VIEWPORT.y + 120)))
    t = pygame.time.get_ticks() / 1000
    screen.set_clip(LOCKER_VIEWPORT)
    for i, item in enumerate(items):
        card, button = card_rects(i, LOCKER_VIEWPORT, locker_scroll)
        if card.bottom < LOCKER_VIEWPORT.top or card.top > LOCKER_VIEWPORT.bottom:
            continue
        equipped = item == current_skin
        draw_shop_card(card, button, "SKIN", None, item.capitalize(),
                       GREEN if equipped else BLUE, "Equipped" if equipped else "Equip")
        draw_skin_preview(card, item, t, i)
    screen.set_clip(None)
    draw_scrollbar(LOCKER_VIEWPORT, locker_scroll, max_card_scroll(len(items), LOCKER_VIEWPORT))

def handle_locker_tab_click(pos):
    global current_skin
    if not LOCKER_VIEWPORT.collidepoint(pos):
        return
    for i, item in enumerate(locker_items()):
        _, button = card_rects(i, LOCKER_VIEWPORT, locker_scroll)
        if button.collidepoint(pos):
            current_skin = item
            return

# ---- The hub itself ----
def draw_hub():
    draw_shop_header(hub_tab.upper(), None if in_shooting_range else main_game_coins)
    for tab, rect in HUB_TAB_RECTS.items():
        draw_button(rect, YELLOW if tab == hub_tab else BLUE)
        text = smaller_button_font.render(tab, True, BLACK)
        screen.blit(text, text.get_rect(center=rect.center))
    if hub_tab == "Play":
        draw_play_tab()
    elif hub_tab == "Shop":
        draw_shop_tab()
    elif hub_tab == "Upgrades":
        draw_upgrades_tab()
    elif hub_tab == "Abilities":
        draw_abilities_tab()
    elif hub_tab == "Locker":
        draw_locker_tab()
    elif hub_tab == "Settings":
        draw_settings_content()

def handle_hub_event(event):
    global hub_open, start_screen, hub_tab
    global shop_upgrade_scroll_target, ability_scroll_target, locker_scroll_target
    if event.type == pygame.MOUSEWHEEL:
        step = event.y * 80
        if hub_tab == "Upgrades":
            shop_upgrade_scroll_target = max(0, min(max_card_scroll(len(SHOP_UPGRADES), SHOP_UPGRADE_VIEWPORT),
                                                    shop_upgrade_scroll_target - step))
        elif hub_tab == "Abilities":
            ability_scroll_target = max(0, min(max_card_scroll(len(ABILITIES), HUB_VIEWPORT),
                                               ability_scroll_target - step))
        elif hub_tab == "Locker":
            locker_scroll_target = max(0, min(max_card_scroll(len(locker_items()), LOCKER_VIEWPORT),
                                              locker_scroll_target - step))
        return
    if hub_tab == "Play" and event.type == pygame.KEYDOWN and handle_lobby_key(event):
        return
    if hub_tab == "Settings":
        handle_settings_content_event(event)  # Needs the raw event for its confirm boxes
    if event.type != pygame.MOUSEBUTTONDOWN or event.button != 1:
        return
    pos = pygame.mouse.get_pos()
    if settings_confirm and hub_tab == "Settings":
        return  # The confirm box has the screen
    for tab, rect in HUB_TAB_RECTS.items():
        if not rect.collidepoint(pos):
            continue
        if tab == "Main Menu":
            hub_open = False
            start_screen = True
        else:
            hub_tab = tab
        return
    if hub_tab == "Play":
        handle_play_tab_click(pos)
    elif hub_tab == "Shop":
        handle_shop_tab_click(pos)
    elif hub_tab == "Upgrades":
        handle_upgrades_tab_click(pos)
    elif hub_tab == "Abilities":
        handle_abilities_tab_click(pos)
    elif hub_tab == "Locker":
        handle_locker_tab_click(pos)

# ---- Tutorial mode ----
in_tutorial = False
tutorial_step = 0
tutorial_state = {}
shots_fired = 0
TUTORIAL_STEPS = [
    "Use W A S D to move around",
    "Aim with the mouse and left click to shoot",
    "Shoot the three red enemies",
    "Walk over the coins they drop to collect them",
    "Press Escape any time for the pause menu",
]

def advance_tutorial():
    global tutorial_step, tutorial_state
    tutorial_step += 1
    tutorial_state = {}

def update_tutorial(dt):
    """Move through the tutorial steps as the player does each thing."""
    global tutorial_state
    if tutorial_step >= len(TUTORIAL_STEPS):
        tutorial_state["done"] = tutorial_state.get("done", 0.0) + dt
        if tutorial_state["done"] > 3.0:
            exit_to_main_menu()
        return
    if tutorial_step == 0:
        tutorial_state.setdefault("start", (player_x, player_y))
        if math.hypot(player_x - tutorial_state["start"][0], player_y - tutorial_state["start"][1]) > 120:
            advance_tutorial()
    elif tutorial_step == 1:
        tutorial_state.setdefault("shots", shots_fired)
        if shots_fired - tutorial_state["shots"] >= 3:
            advance_tutorial()
    elif tutorial_step == 2:
        if not tutorial_state.get("spawned"):
            tutorial_state["spawned"] = True
            for _ in range(3):
                red_enemies.append(get_safe_enemy_spawn())
        elif not red_enemies:
            advance_tutorial()
    elif tutorial_step == 3:
        tutorial_state.setdefault("coins", coin_count)
        if coin_count > tutorial_state["coins"] or not coins:
            advance_tutorial()
    elif tutorial_step == 4:
        tutorial_state["timer"] = tutorial_state.get("timer", 0.0) + dt
        if tutorial_state["timer"] > 4.0:
            advance_tutorial()

def draw_tutorial_banner():
    """The current instruction, in a panel under the ability badge."""
    if tutorial_step >= len(TUTORIAL_STEPS):
        text, color = "Tutorial complete!", (150, 255, 170)
    else:
        text, color = TUTORIAL_STEPS[tutorial_step], WHITE
    label = button_font.render(text, True, color)
    panel = label.get_rect(center=(WIDTH // 2, 210)).inflate(56, 30)  # Clear of the ability badge and toasts
    draw_panel(panel, radius=14)
    screen.blit(label, label.get_rect(center=panel.center))
    if tutorial_step < len(TUTORIAL_STEPS):
        step_text = small_button_font.render(f"Step {tutorial_step + 1} of {len(TUTORIAL_STEPS)}", True, (205, 210, 216))
        screen.blit(step_text, step_text.get_rect(center=(WIDTH // 2, panel.bottom + 18)))


enemy_radius = player_size // 2
red_orb = create_orb_sprite((225, 35, 35), enemy_radius)
green_orb = create_orb_sprite((110, 235, 70), enemy_radius)  # Lime so it stands out from the grass
blue_orb = create_orb_sprite((45, 95, 245), enemy_radius)
purple_orb = create_orb_sprite((150, 60, 215), enemy_radius)
orange_orb = create_orb_sprite((255, 140, 30), enemy_radius)
yellow_orb = create_orb_sprite((245, 215, 40), enemy_radius)
teal_orb = create_orb_sprite((40, 215, 200), enemy_radius)
pink_orb = create_orb_sprite((255, 105, 180), enemy_radius)
violet_orb = create_orb_sprite((190, 150, 255), enemy_radius)  # Light violet, so it doesn't look like a purple
purple_mini_orb = create_orb_sprite((175, 90, 235), purple_mini_size // 2, glow=5)
enemy_shadow = create_shadow_sprite(enemy_radius)
mini_shadow = create_shadow_sprite(purple_mini_size // 2)
# Fading copies of the green orb for its speed trail (nearest first)
green_trail = []
for trail_alpha in (120, 75, 40):
    ghost = green_orb.copy()
    ghost.set_alpha(trail_alpha)
    green_trail.append(ghost)

def get_safe_enemy_spawn():
    """A random spot inside the barrier that is off screen, so nothing appears on top of the player.
    If the play area is too small for that (late Barrier Shrink), the farthest spot found is used."""
    barrier_thickness = 12  # Must match the value used for drawing the barrier
    if in_storm_survival:
        left = MAP_WIDTH // 2 - storm_survival_map_width // 2
        top = MAP_HEIGHT // 2 - storm_survival_map_height // 2
        right, bottom = left + storm_survival_map_width, top + storm_survival_map_height
    else:
        left, top, right, bottom = 0, 0, MAP_WIDTH, MAP_HEIGHT
    low_x, high_x = left + barrier_thickness, max(left + barrier_thickness, right - player_size - barrier_thickness)
    low_y, high_y = top + barrier_thickness, max(top + barrier_thickness, bottom - player_size - barrier_thickness)
    px, py = player_x + player_size / 2, player_y + player_size / 2
    # Players are always in the middle of their screens, so "off screen" is outside this box around every player
    views = []
    for top_x, top_y in ([(player_x, player_y)] + ([(p["x"], p["y"]) for p in remote_players.values()] if multiplayer_match else [])):
        view = pygame.Rect(0, 0, WIDTH + 2 * player_size + 120, HEIGHT + 2 * player_size + 120)
        view.center = (top_x + player_size / 2, top_y + player_size / 2)
        views.append(view)
    best, best_dist = None, -1.0
    for _ in range(300):
        ex, ey = random.randint(low_x, high_x), random.randint(low_y, high_y)
        if not any(view.collidepoint(ex + player_size / 2, ey + player_size / 2) for view in views):
            return [ex, ey]
        dist = min(math.hypot(ex + player_size / 2 - v.centerx, ey + player_size / 2 - v.centery) for v in views)
        if dist > best_dist:
            best, best_dist = [ex, ey], dist
    return best

def update_purple_minis(i):
    """Place purple enemy i's mini circles around it at their current angles."""
    ex, ey = purple_enemies[i]
    center_x = ex + player_size // 2
    center_y = ey + player_size // 2
    for mini in purple_mini_circles[i]:
        mini[0] = center_x + purple_mini_tether * math.cos(mini[2])
        mini[1] = center_y + purple_mini_tether * math.sin(mini[2])

def spawn_purple():
    """Spawn a big purple enemy with 4 mini circles tethered to it."""
    purple_enemies.append(get_safe_enemy_spawn())
    purple_mini_circles.append([[0, 0, k * math.pi / 2] for k in range(4)])
    update_purple_minis(len(purple_enemies) - 1)

def remove_purple(i):
    """Remove purple enemy i along with its mini circles."""
    purple_enemies.pop(i)
    purple_mini_circles.pop(i)

def lerp_color(c1, c2, t):
    """Linear interpolate between two RGB colors"""
    return (
        int(c1[0] + (c2[0] - c1[0]) * t),
        int(c1[1] + (c2[1] - c1[1]) * t),
        int(c1[2] + (c2[2] - c1[2]) * t),
    )

def rainbow_color_cycle(elapsed_time, cycle_duration=2.0):
    """Return a smoothly cycling rainbow RGB color based on elapsed time."""
    # Define 6 rainbow colors in order
    rainbow_colors = [
        (148, 0, 211),  # violet
        (75, 0, 130),   # indigo
        (0, 0, 255),    # blue
        (0, 255, 0),    # green
        (255, 255, 0),  # yellow
        (255, 127, 0),  # orange
        (255, 0, 0)    # red - optional to loop fully or keep 6 colors
    ]
    # total segments
    n = len(rainbow_colors) - 1
    total_time = cycle_duration
    t = (elapsed_time % total_time) / total_time * n
    i = int(t)
    frac = t - i
    c1 = rainbow_colors[i]
    c2 = rainbow_colors[(i + 1) % len(rainbow_colors)]
    return lerp_color(c1, c2, frac)

def reset_game(shooting_range=False, storm_survival=False, block_defence=False, tutorial=False):
    global player_x, player_y, angle, last_rot_angle, bullets, game_over, coins, player_color, mini_color
    global red_enemies, green_enemies, blue_enemies, kills, wave, max_red_enemies, max_green_enemies, max_blue_enemies, coin_count, in_shooting_range, in_storm_survival, in_block_defence, blue_last_shot_times, teleport_cooldown
    global freeze_active, freeze_cooldown, freeze_timer, wave_completion_message, wave_completion_timer, last_wave, game_paused, pause_countdown, purple_enemies, max_purple_enemies, purple_mini_circles
    global game_timer, helpers, helpers_active, helpers_cooldown, helpers_timer
    global triple_bullet_active, triple_bullet_cooldown, triple_bullet_timer, wave_spawning
    global shooting_range_editor_mode, shooting_range_play_mode, camera_x, camera_y
    global storm_survival_won, in_tutorial, tutorial_step, tutorial_state
    in_tutorial = tutorial
    tutorial_step = 0
    tutorial_state = {}
    wave_spawning = False
    wave = 0
    player_x = MAP_WIDTH // 2 - player_size // 2
    player_y = MAP_HEIGHT // 2 - player_size // 2 + 300
    angle = 0
    last_rot_angle = 0
    
    # Set camera to center on player
    camera_x = player_x - WIDTH // 2 + player_size // 2
    camera_y = player_y - HEIGHT // 2 + player_size // 2
    bullets = []
    blue_bullets.clear()  # Every flying shot is gone when you (re)start
    coins.clear()
    effects.clear()
    orange_enemies.clear()
    yellow_enemies.clear()
    teal_enemies.clear()
    pink_enemies.clear()
    violet_enemies.clear()
    storm_spawn_seconds.clear()
    globals()['active_boss'] = None
    boss_push[:] = [0.0, 0.0]
    game_over = False
    in_shooting_range = shooting_range
    if shooting_range:
        globals()["sandbox_entry_coins"] = main_game_coins
    in_storm_survival = storm_survival
    in_block_defence = block_defence
    # Reset block health for Block Defence mode (only when starting a new game)
    if block_defence:
        # Only reset block health if it's the initial game start, not when returning from shop
        if not hasattr(reset_game, 'block_health_initialized') or not reset_game.block_health_initialized:
            globals()['block_health'] = 50
            reset_game.block_health_initialized = True
        globals()['block_defence_game_over_timer'] = 0.0
        globals()['block_defence_points'] = 0
    # Initialize storm survival map size
    if storm_survival:
        global storm_survival_map_width, storm_survival_map_height
        storm_survival_map_width = MAP_WIDTH
        storm_survival_map_height = MAP_HEIGHT
        storm_survival_won = False
    teleport_cooldown = 0.0
    freeze_active = False
    freeze_cooldown = 0.0
    freeze_timer = 0.0
    # Set player color depending on skin
    if current_skin == "rainbow":
        player_color = WHITE
        mini_color = WHITE
    else:
        player_color = skin_colors.get(current_skin, WHITE)
        mini_color = player_color
    kills = 0
    if shooting_range or storm_survival or block_defence or tutorial:
        red_enemies = []
        green_enemies = []
        blue_enemies = []
        purple_enemies = []
        purple_mini_circles = []
        blue_last_shot_times = []
        wave = 1
        max_red_enemies = 0
        max_green_enemies = 0
        max_blue_enemies = 0
        max_purple_enemies = 0
        # Set coin count based on game mode
        if block_defence:
            coin_count = block_defence_coins
        else:
            coin_count = main_game_coins
        wave_completion_message = ""
        wave_completion_timer = 0.0
        last_wave = 1
        game_paused = False
        pause_countdown = 0.0
        game_timer = 0.0
        helpers.clear()
        helpers_active = False
        helpers_cooldown = 0.0
        helpers_timer = 0.0
        triple_bullet_active = False
        triple_bullet_cooldown = 0.0
        triple_bullet_timer = 0.0
        shooting_range_editor_mode = True
        shooting_range_play_mode = False
    else:
        red_enemies = [get_safe_enemy_spawn() for _ in range(WAVES[1]["red"])]
        green_enemies = []
        blue_enemies = []
        purple_enemies = []
        purple_mini_circles = []
        blue_last_shot_times = []
        wave = 1
        max_red_enemies = 1
        max_green_enemies = 0
        max_blue_enemies = 0
        max_purple_enemies = 0
        wave_completion_message = ""
        wave_completion_timer = 0.0
        last_wave = 1
        game_paused = False
        pause_countdown = 0.0
        game_timer = 0.0
        helpers.clear()
        helpers_active = False
        helpers_cooldown = 0.0
        helpers_timer = 0.0
        triple_bullet_active = False
        triple_bullet_cooldown = 0.0
        triple_bullet_timer = 0.0
        shooting_range_editor_mode = True
        shooting_range_play_mode = False

reset_game()

orbit_radius = 60

running = True
# Log straight in if this device remembers an account
_remembered_online = cube_accounts.remembered_online() if ONLINE_ACCOUNTS else None
_remembered_account = None if ONLINE_ACCOUNTS else cube_accounts.remembered_account(save_data)
if _remembered_online is not None:
    login_fields["username"] = _remembered_online[0]
    try:
        show_login_status("Logging in...")
        online_session, _progress = cube_online.resume(_remembered_online[1])
        login_remember = True
        log_in_as({"name": online_session.name, "progress": newest_progress(online_session, _progress)},
                  f"Welcome back, {online_session.name}!")
    except cube_online.OfflineError:
        login_message, login_message_ok = "Can't reach the server - check your internet", False
    except cube_online.ServerError:
        cube_accounts.forget_remembered(save_data)  # Token expired or account gone: log in normally
        login_message, login_message_ok = "", False
if _remembered_account is not None:
    login_remember = True
    log_in_as(_remembered_account, f"Welcome back, {_remembered_account['name']}!")

was_game_over = False
while running:
    dt = clock.tick(60) / 1000
    update_multiplayer()
    if game_over and not was_game_over:
        sounds.play("player_death")  # However the player died, the death sound plays once
    was_game_over = game_over

    # A downloaded update gets installed as soon as you're on a menu (never in the middle of a game)
    if auto_updater.state == "ready" and (login_screen_open or start_screen or hub_open or settings_open):
        save_current_account()
        if updater.install(auto_updater.staged):
            auto_updater.state = "installing"
            running = False
            break
        auto_updater.state = "failed"

    # Login screen (shown at startup and after logging out) runs on its own
    if login_screen_open:
        login_screen_frame(pygame.event.get())
        draw_update_status()
        pygame.display.flip()
        continue


    screen.fill(BLACK)
    events = pygame.event.get()  # Only call this ONCE per frame

    # Keep coins and the main-game copies in sync, and autosave the logged-in account when anything changes
    update_progress_and_autosave()

    # Menus get a metal background; the game world gets grass and the map barrier.
    # During game over the world stays visible (slowly zooming out) unless a menu like the shop is open.
    if not game_over:
        death_snapshot = None
    in_menu = (start_screen
               or hub_open or settings_open or (game_over and death_snapshot is None))
    if in_menu:
        screen.blit(metal_background, (0, 0))
    else:
        draw_world_background(game_over_zoom() if game_over else 1.0)

    for event in events:
        if event.type == pygame.QUIT:
            running = False

        # Code console: ` drops the typing bar down from the top, on any screen or game mode
        if event.type == pygame.KEYDOWN and (event.key == pygame.K_BACKQUOTE or event.unicode == "`"):
            if console_open or admin_code_open or admin_panel_open:
                close_console_stack()
            else:
                console_open = True
                console_input = ""
                console_was_paused = game_paused
                game_paused = True  # Freeze the game while typing
            continue
        if enemy_menu_open and not console_open and not admin_code_open and not admin_panel_open:
            handle_enemy_menu_event(event)
            continue
        if block_menu_open and not console_open and not admin_code_open and not admin_panel_open:
            handle_block_menu_event(event)
            continue
        # Block Defence: clicking the block opens its repair menu (instead of shooting)
        if (in_block_defence and not game_over and not game_paused and event.type == pygame.MOUSEBUTTONDOWN
                and event.button == 1 and not console_open and not pause_menu_open
                and BLOCK_DEFENCE_BLOCK_RECT.move(-camera_x, -camera_y).collidepoint(pygame.mouse.get_pos())):
            open_block_menu()
            continue
        # Escape opens the pause menu during a game (the console and admin screens get it first)
        if (event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE and not console_open
                and not admin_code_open and not admin_panel_open and not in_menu and not game_over):
            close_pause_menu() if pause_menu_open else open_pause_menu()
            continue
        if pause_menu_open:
            handle_pause_menu_event(event)
            continue
        if admin_panel_open:
            if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                pos = pygame.mouse.get_pos()
                if ADMIN_GIVE_BUTTON.collidepoint(pos):
                    admin_give_everything()
                elif ADMIN_SHOP_BUTTON.collidepoint(pos):
                    admin_change_shop()
                elif ADMIN_CLOSE_BUTTON.collidepoint(pos):
                    close_console_stack()
            elif event.type == pygame.KEYDOWN and event.key == pygame.K_ESCAPE:
                close_console_stack()
            continue
        if admin_code_open:
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    close_console_stack()
                elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                    if admin_code_input == ADMIN_CODE:
                        admin_code_open = False
                        admin_panel_open = True
                    else:
                        console_message, console_message_timer = "Wrong code", 2.5
                    admin_code_input = ""
                elif event.key == pygame.K_BACKSPACE:
                    admin_code_input = admin_code_input[:-1]
                elif event.unicode.isdigit() and len(admin_code_input) < 12:
                    admin_code_input += event.unicode
            continue
        if console_open:
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    close_console_stack()
                elif event.key in (pygame.K_RETURN, pygame.K_KP_ENTER):
                    run_console_command(console_input)
                elif event.key == pygame.K_BACKSPACE:
                    console_input = console_input[:-1]
                elif event.unicode.isprintable() and event.unicode != "`" and len(console_input) < 24:
                    console_input += event.unicode
            continue  # While the console is open, ignore all other input

        # Global key handling (works in all modes)
        if event.type == pygame.KEYDOWN:
            if event.key == pygame.K_l and coin_cheat_enabled:
                coin_count += 1000
                if not in_shooting_range:
                    main_game_coins = coin_count  # Update main game coins
            elif event.key == pygame.K_F11:
                pygame.display.toggle_fullscreen()  # True full screen on/off
            elif event.key == pygame.K_m and no_death_cheat_enabled:
                invincible = not invincible  # Toggle invincibility
            elif event.key == pygame.K_k and kill_cheat_enabled:
                # Kill all enemies (they all burst apart)
                for kind, group in dict_enemy_groups():
                    for enemy in group:
                        spawn_death_effect(enemy["x"] + player_size // 2, enemy["y"] + player_size // 2, kind)
                    group.clear()
                for kind, group in (("red", red_enemies), ("green", green_enemies), ("blue", blue_enemies), ("purple", purple_enemies)):
                    for ex, ey in group:
                        spawn_death_effect(ex + player_size // 2, ey + player_size // 2, kind)
                red_enemies.clear()
                green_enemies.clear()
                blue_enemies.clear()
                blue_last_shot_times.clear()
                purple_enemies.clear()
                purple_mini_circles.clear()
            elif event.key == pygame.K_p and (not start_screen and not game_over
                                              and not hub_open
                                              and not settings_open):
                if game_paused:
                    # Start countdown to unpause
                    pause_countdown = pause_countdown_duration
                else:
                    # Pause the game
                    game_paused = True

        if settings_open:
            handle_settings_event(event)
            continue
        elif hub_open:
            handle_hub_event(event)
            continue
        elif start_screen:
            if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                mx, my = pygame.mouse.get_pos()
                if current_account is not None and LOGOUT_BUTTON.collidepoint(mx, my):
                    log_out()
                for name, rect in main_menu_buttons():
                    if not rect.collidepoint(mx, my):
                        continue
                    if name == "Play":
                        start_screen = False
                        hub_open = True
                        hub_tab = "Play"
                    elif name == "Settings":
                        start_screen = False
                        settings_open = True
                        settings_confirm = None
                    elif name == "Quit":
                        pygame.quit()
                        sys.exit()
            continue  # Skip further event handling if on start screen



        elif not game_over:
            if event.type == pygame.MOUSEBUTTONDOWN:
                mx, my = pygame.mouse.get_pos()
                

                if event.button == 1:  # Only left mouse button
                    # Don't shoot in editor mode
                    if not (in_shooting_range and shooting_range_editor_mode):
                        current_time = pygame.time.get_ticks() / 1000
                        if current_time - last_shot_time >= shot_delay:
                            bullet_speed = 10
                            center_x = orbit_x + mini_size // 2
                            center_y = orbit_y + mini_size // 2
                            tip_offset = mini_size // 2
                            
                            if triple_bullet_active:
                                # Shoot three bullets in a spread pattern
                                angles = [last_rot_angle - 0.3, last_rot_angle, last_rot_angle + 0.3]  # 30-degree spread
                                for angle in angles:
                                    bullet_dx = math.cos(angle) * bullet_speed
                                    bullet_dy = math.sin(angle) * bullet_speed
                                    bullet_x = center_x + math.cos(angle) * tip_offset
                                    bullet_y = center_y + math.sin(angle) * tip_offset
                                    bullets.append({"x": bullet_x, "y": bullet_y, "dx": bullet_dx, "dy": bullet_dy})
                            else:
                                # Shoot single bullet
                                bullet_dx = math.cos(last_rot_angle) * bullet_speed
                                bullet_dy = math.sin(last_rot_angle) * bullet_speed
                                bullet_x = center_x + math.cos(last_rot_angle) * tip_offset
                                bullet_y = center_y + math.sin(last_rot_angle) * tip_offset
                                bullets.append({"x": bullet_x, "y": bullet_y, "dx": bullet_dx, "dy": bullet_dy})
                            
                            last_shot_time = current_time
                            shots_fired += 1
                            sounds.play("shoot", 0.6)
        

        # Bottom-left mode buttons, plus the Shooting Range play/editor toggle
        if not game_over and not start_screen:
            if event.type == pygame.MOUSEBUTTONDOWN and event.button == 1:
                mx, my = pygame.mouse.get_pos()
                for name, rect, _, _ in game_button_rects():
                    if not rect.collidepoint(mx, my):
                        continue
                    if name == "Add Enemies":
                        open_enemy_menu()
                    game_paused = True
                if in_shooting_range:
                    play_button = pygame.Rect(WIDTH - 120, HEIGHT - 60, 100, 40)
                    if play_button.collidepoint(mx, my):
                        shooting_range_editor_mode = not shooting_range_editor_mode
                        shooting_range_play_mode = not shooting_range_editor_mode
                        if shooting_range_play_mode:
                            sandbox_snapshot = snapshot_sandbox()  # What Retry will bring back



        # Shield activation (disabled in editor mode)
        if has_shield and event.type == pygame.MOUSEBUTTONDOWN and event.button == 3 and not (in_shooting_range and shooting_range_editor_mode):
            if shield_cooldown <= 0 and not shield_active:
                shield_active = True
                shield_timer = 0.0
                sounds.play("shield")
        if has_shield and event.type == pygame.MOUSEBUTTONUP and event.button == 3 and not (in_shooting_range and shooting_range_editor_mode):
            if shield_active:
                shield_active = False
                if shield_timer > 0:
                    # If released early, cooldown is double the time held
                    shield_cooldown = min(shield_cooldown_time, shield_timer * 2)
                    shield_timer = 0
        # Teleport ability (disabled in editor mode)
        if has_teleport and equipped_ability == 'teleport' and event.type == pygame.MOUSEBUTTONDOWN and event.button == 3 and not (in_shooting_range and shooting_range_editor_mode):
            if teleport_cooldown <= 0:
                mx, my = pygame.mouse.get_pos()
                teleport_from = (player_x + player_size / 2, player_y + player_size / 2)
                # Convert screen coordinates to world coordinates
                world_x = mx + camera_x
                world_y = my + camera_y
                player_x = world_x - player_size // 2
                player_y = world_y - player_size // 2
                # Clamp to map boundaries
                if in_storm_survival:
                    # Use shrinking map boundaries for storm survival, centered on original map center
                    center_x = MAP_WIDTH // 2
                    center_y = MAP_HEIGHT // 2
                    map_left = center_x - storm_survival_map_width // 2
                    map_top = center_y - storm_survival_map_height // 2
                    map_right = center_x + storm_survival_map_width // 2
                    map_bottom = center_y + storm_survival_map_height // 2
                    player_x = max(map_left, min(map_right - player_size, player_x))
                    player_y = max(map_top, min(map_bottom - player_size, player_y))
                else:
                    # Use normal map boundaries for other modes
                    player_x = max(0, min(MAP_WIDTH - player_size, player_x))
                    player_y = max(0, min(MAP_HEIGHT - player_size, player_y))
                # Flash of light where you left and where you land
                spawn_teleport_flash(teleport_from[0], teleport_from[1],
                                     player_x + player_size / 2, player_y + player_size / 2)
                # Start cooldown
                teleport_cooldown = teleport_cooldown_time
        # Freeze ability (disabled in editor mode)
        if has_freeze and equipped_ability == 'freeze' and event.type == pygame.MOUSEBUTTONDOWN and event.button == 3 and not (in_shooting_range and shooting_range_editor_mode):
            if freeze_cooldown <= 0:
                freeze_active = True
                freeze_timer = 0.0
                freeze_cooldown = freeze_cooldown_time
        # Helpers ability (disabled in editor mode)
        if has_helpers and equipped_ability == 'helpers' and event.type == pygame.MOUSEBUTTONDOWN and event.button == 3 and not (in_shooting_range and shooting_range_editor_mode):
            if helpers_cooldown <= 0:
                helpers_active = True
                helpers_timer = 0.0
                helpers_cooldown = helpers_cooldown_time
                # Spawn 2 helpers near the player
                helpers.clear()
                for i in range(2):
                    # Spawn helpers at different positions around the player
                    angle = (i * 2 * math.pi) / 2  # Evenly spaced around the circle
                    offset_x = 50 * math.cos(angle)  # 50 pixels away from center
                    offset_y = 50 * math.sin(angle)  # 50 pixels away from center
                    helper_x = player_x + player_size // 2 + offset_x - helper_size // 2
                    helper_y = player_y + player_size // 2 + offset_y - helper_size // 2
                    helpers.append({
                        "x": helper_x,
                        "y": helper_y,
                        "angle": 0,
                        "last_shot_time": 0,
                        "skin": current_skin
                    })
        # Shockwave ability (disabled in editor mode)
        if has_shockwave and equipped_ability == 'shockwave' and event.type == pygame.MOUSEBUTTONDOWN and event.button == 3 and not (in_shooting_range and shooting_range_editor_mode):
            if shockwave_cooldown <= 0:
                shockwave_active = True
                shockwave_timer = 0.0
                shockwave_cooldown = shockwave_cooldown_time
                spawn_death_effect(player_x + player_size / 2, player_y + player_size / 2, "purple", (190, 90, 255))
        # Coin Controller ability (disabled in editor mode)
        if has_coin_controller and equipped_ability == 'coin_controller' and event.type == pygame.MOUSEBUTTONDOWN and event.button == 3 and not (in_shooting_range and shooting_range_editor_mode):
            if coin_controller_cooldown <= 0 and not coin_controller_active:
                coin_controller_active = True
                coin_controller_timer = 0.0
                # Don't start cooldown yet - wait for all coins to be collected
        
        
        # Triple Bullet ability (disabled in editor mode)
        if has_triple_bullet and equipped_ability == 'triple_bullet' and event.type == pygame.MOUSEBUTTONDOWN and event.button == 3 and not (in_shooting_range and shooting_range_editor_mode):
            if triple_bullet_cooldown <= 0:
                triple_bullet_active = True
                triple_bullet_timer = 0.0
                triple_bullet_cooldown = triple_bullet_cooldown_time

    if start_screen:
        # Bubbly two-line title ("Cube" on top of "Shooter") that gently bobs up and down
        bob_time = pygame.time.get_ticks() / 500
        cube_y = 60 + math.sin(bob_time) * 6
        shooter_y = 60 + title_cube_surface.get_height() - 40 + math.sin(bob_time + 1.2) * 6
        screen.blit(title_shooter_surface, (WIDTH // 2 - title_shooter_surface.get_width() // 2, shooter_y))
        screen.blit(title_cube_surface, (WIDTH // 2 - title_cube_surface.get_width() // 2, cube_y))
        chapter_text = get_bubble_text("Chapter 2", 44, (225, 240, 255), (110, 160, 225), outline=6)
        screen.blit(chapter_text, (WIDTH // 2 - chapter_text.get_width() // 2, shooter_y + title_shooter_surface.get_height() - 34))

        # Main menu buttons: Game Modes, Locker, Shop, Tutorial, Quit
        for name, rect in main_menu_buttons():
            draw_button(rect, RED if name == "Quit" else BLUE)
            label = button_font.render(name, True, BLACK)
            screen.blit(label, label.get_rect(center=rect.center))

        code_hint = small_button_font.render("Press ` at any time to enter a code", True, (205, 210, 216))
        screen.blit(code_hint, (WIDTH // 2 - code_hint.get_width() // 2, HEIGHT - 30))
        draw_account_bar()
        draw_update_status()

    elif settings_open:
        draw_settings()

    elif hub_open:
        draw_hub()


    elif not game_over:
        keys = pygame.key.get_pressed()
        
        # Handle movement based on mode
        if in_shooting_range and shooting_range_editor_mode:
            # Editor mode: Camera controls
            camera_speed = 8
            if keys[pygame.K_w]: camera_y -= camera_speed
            if keys[pygame.K_s]: camera_y += camera_speed
            if keys[pygame.K_a]: camera_x -= camera_speed
            if keys[pygame.K_d]: camera_x += camera_speed
        else:
            # Play mode: Player movement
            if not game_paused:
                if keys[pygame.K_w]: player_y -= player_speed
                if keys[pygame.K_s]: player_y += player_speed
                if keys[pygame.K_a]: player_x -= player_speed
                if keys[pygame.K_d]: player_x += player_speed

        # Update camera to follow player for unlimited map (only in play mode)
        if not (in_shooting_range and shooting_range_editor_mode):
            camera_x = player_x - WIDTH // 2 + player_size // 2
            camera_y = player_y - HEIGHT // 2 + player_size // 2

        # Clamp player position to map boundaries
        if in_storm_survival:
            # Use shrinking map boundaries for storm survival, centered on original map center
            center_x = MAP_WIDTH // 2
            center_y = MAP_HEIGHT // 2
            map_left = center_x - storm_survival_map_width // 2
            map_top = center_y - storm_survival_map_height // 2
            map_right = center_x + storm_survival_map_width // 2
            map_bottom = center_y + storm_survival_map_height // 2
            player_x = max(map_left, min(map_right - player_size, player_x))
            player_y = max(map_top, min(map_bottom - player_size, player_y))
        else:
            # Use normal map boundaries for other modes
            player_x = max(0, min(MAP_WIDTH - player_size, player_x))
            player_y = max(0, min(MAP_HEIGHT - player_size, player_y))

        # Block Defence block collision
        if in_block_defence:
            player_rect = pygame.Rect(player_x, player_y, player_size, player_size)
            block_rect = BLOCK_DEFENCE_BLOCK_RECT
            if player_rect.colliderect(block_rect):
                # Calculate previous position
                if 'prev_player_x' not in globals():
                    prev_player_x = player_x
                if 'prev_player_y' not in globals():
                    prev_player_y = player_y
                # Determine direction and push player out
                if prev_player_y + player_size <= block_rect.y:
                    player_y = block_rect.y - player_size
                elif prev_player_y >= block_rect.y + block_rect.height:
                    player_y = block_rect.y + block_rect.height
                elif prev_player_x + player_size <= block_rect.x:
                    player_x = block_rect.x - player_size
                elif prev_player_x >= block_rect.x + block_rect.width:
                    player_x = block_rect.x + block_rect.width
            prev_player_x = player_x
            prev_player_y = player_y

        if in_tutorial and not game_paused:
            update_tutorial(dt)

        # Wave progression logic (only in main game, not shooting range, storm survival, or block defence)
        global wave_spawning
        if not in_shooting_range and not in_storm_survival and not in_block_defence and not in_tutorial and net_role() != "guest":
            # Only trigger wave spawn if all enemy lists are empty and not already spawning
            if (not wave_spawning and
                len(red_enemies) == 0 and len(green_enemies) == 0 and len(blue_enemies) == 0 and
                len(purple_enemies) == 0 and active_boss is None and not orange_enemies and not yellow_enemies and not teal_enemies and not pink_enemies and not violet_enemies):
                wave_spawning = True
                wave += 1
                spawn_counts = wave_spawn_counts(wave)
                if not wave_jump_pending:  # A wave# jump isn't a finished wave: no banner, coins or best wave
                    finished_boss_wave = bool(WAVES.get(wave - 1, {}).get("boss"))
                    wave_completion_message = "Boss Wave Completed!" if finished_boss_wave else f"Wave {wave - 1} Complete!"
                    wave_completion_reward = BOSSES[WAVES[wave - 1]["boss"]]["reward"] if finished_boss_wave else 15
                    sounds.play("boss_wave_complete" if finished_boss_wave else "wave_complete")
                    best_wave = max(best_wave, wave - 1)  # Saved to the account
                    wave_completion_timer = wave_completion_duration
                    coin_count += wave_completion_reward
                    main_game_coins = coin_count
                    if net_role() == "host":
                        net_events.append(["wave", wave_completion_reward, finished_boss_wave, wave - 1])
                wave_jump_pending = False
                # Clear all enemies for new wave (should already be empty)
                red_enemies.clear()
                green_enemies.clear()
                blue_enemies.clear()
                blue_last_shot_times.clear()
                purple_enemies.clear()
                purple_mini_circles.clear()
                # Spawn new enemies for the wave (no sleep)
                for _ in range(spawn_counts['red']):
                    red_enemies.append(get_safe_enemy_spawn())
                for _ in range(spawn_counts['green']):
                    green_enemies.append(get_safe_enemy_spawn())
                for _ in range(spawn_counts['blue']):
                    blue_enemies.append(get_safe_enemy_spawn())
                    blue_last_shot_times.append(0)
                for _ in range(spawn_counts['purple']):
                    spawn_purple()
                for _ in range(spawn_counts['orange']):
                    orange_enemies.append(new_orange_enemy(*get_safe_enemy_spawn()))
                for _ in range(spawn_counts['yellow']):
                    yellow_enemies.append(new_yellow_enemy(*get_safe_enemy_spawn()))
                for _ in range(spawn_counts.get('teal', 0)):
                    teal_enemies.append(new_teal_enemy(*get_safe_enemy_spawn()))
                for _ in range(spawn_counts.get('pink', 0)):
                    pink_enemies.append(new_pink_enemy(*get_safe_enemy_spawn()))
                for _ in range(spawn_counts.get('violet', 0)):
                    violet_enemies.append(new_violet_enemy(*get_safe_enemy_spawn()))
                if spawn_counts.get('boss'):
                    spawn_boss(spawn_counts['boss'])
                wave_spawning = False
                
        # Only update game logic if not paused and in play mode
        if not game_paused and not (in_shooting_range and shooting_range_editor_mode):
            player_center = (player_x + player_size // 2, player_y + player_size // 2)
            mouse_x, mouse_y = pygame.mouse.get_pos()
            world_mouse_x = mouse_x + camera_x
            world_mouse_y = mouse_y + camera_y
            desired_angle = math.atan2(world_mouse_y - player_center[1], world_mouse_x - player_center[0])
            
            # Always calculate angle and orbit position for drawing
            angle = desired_angle
            orbit_x = player_center[0] + orbit_radius * math.cos(angle) - mini_size // 2
            orbit_y = player_center[1] + orbit_radius * math.sin(angle) - mini_size // 2
            
            # Only update last_rot_angle when not paused (for shooting)
            last_rot_angle = angle

            # Only move enemies if freeze is not active
            if not (has_freeze and equipped_ability == 'freeze' and freeze_active):
                for i in range(len(red_enemies)):
                    ex, ey = red_enemies[i]
                    if in_block_defence:
                        # In Block Defence mode, enemies target the grey block instead of the player
                        block_center_x = BLOCK_DEFENCE_BLOCK_RECT.x + BLOCK_DEFENCE_BLOCK_RECT.width // 2
                        block_center_y = BLOCK_DEFENCE_BLOCK_RECT.y + BLOCK_DEFENCE_BLOCK_RECT.height // 2
                        dx = block_center_x - ex
                        dy = block_center_y - ey
                    else:
                        # Normal mode - enemies target the nearest player
                        target_x, target_y = nearest_player(ex, ey)
                        dx = target_x - ex
                        dy = target_y - ey
                    dist = math.hypot(dx, dy)
                    if dist != 0:
                        dx /= dist
                        dy /= dist
                        ex += dx * red_enemy_speed
                        ey += dy * red_enemy_speed
                    red_enemies[i] = [ex, ey]

                for i in range(len(green_enemies)):
                    ex, ey = green_enemies[i]
                    target_x, target_y = enemy_target(ex, ey)
                    dx = target_x - ex
                    dy = target_y - ey
                    dist = math.hypot(dx, dy)
                    if dist != 0:
                        dx /= dist
                        dy /= dist
                        ex += dx * green_enemy_speed
                        ey += dy * green_enemy_speed
                    green_enemies[i] = [ex, ey]

                for i in range(len(purple_enemies)):
                    ex, ey = purple_enemies[i]
                    target_x, target_y = enemy_target(ex, ey)
                    dx = target_x - ex
                    dy = target_y - ey
                    dist = math.hypot(dx, dy)
                    if dist != 0:
                        dx /= dist
                        dy /= dist
                        ex += dx * purple_enemy_speed
                        ey += dy * purple_enemy_speed
                    purple_enemies[i] = [ex, ey]

                    # Mini circles stay tethered to the big purple and slowly spin around it
                    for mini in purple_mini_circles[i]:
                        mini[2] += purple_mini_spin_speed
                    update_purple_minis(i)

            # Shockwave logic - kill enemies inside the expanding circle
            if has_shockwave and equipped_ability == 'shockwave' and shockwave_active:
                player_center = (player_x + player_size // 2, player_y + player_size // 2)
                # Kill red enemies inside shockwave
                for i in reversed(range(len(red_enemies))):
                    ex, ey = red_enemies[i]
                    enemy_center = (ex + player_size // 2, ey + player_size // 2)
                    if math.hypot(player_center[0] - enemy_center[0], player_center[1] - enemy_center[1]) < shockwave_radius + player_size // 2:
                        red_enemies.pop(i)
                        enemy_killed(ex, ey, "red")
                        kills += 1
                # Kill green enemies inside shockwave
                for i in reversed(range(len(green_enemies))):
                    ex, ey = green_enemies[i]
                    enemy_center = (ex + player_size // 2, ey + player_size // 2)
                    if math.hypot(player_center[0] - enemy_center[0], player_center[1] - enemy_center[1]) < shockwave_radius + player_size // 2:
                        green_enemies.pop(i)
                        enemy_killed(ex, ey, "green")
                        kills += 1
                # Kill blue enemies inside shockwave
                for i in reversed(range(len(blue_enemies))):
                    ex, ey = blue_enemies[i]
                    enemy_center = (ex + player_size // 2, ey + player_size // 2)
                    if math.hypot(player_center[0] - enemy_center[0], player_center[1] - enemy_center[1]) < shockwave_radius + player_size // 2:
                        blue_enemies.pop(i)
                        if i < len(blue_last_shot_times):
                            blue_last_shot_times.pop(i)
                        enemy_killed(ex, ey, "blue")
                        kills += 1
                # Kill orange and yellow enemies inside shockwave
                for kind, group in dict_enemy_groups():
                    for enemy in group[:]:
                        if math.hypot(player_center[0] - (enemy["x"] + player_size // 2),
                                      player_center[1] - (enemy["y"] + player_size // 2)) < shockwave_radius + player_size // 2:
                            group.remove(enemy)
                            enemy_killed(enemy["x"], enemy["y"], kind)
                            kills += 1
                # Kill purple mini circles inside shockwave
                for j in range(len(purple_enemies)):
                    for k in reversed(range(len(purple_mini_circles[j]))):
                        mini_x, mini_y, _ = purple_mini_circles[j][k]
                        if math.hypot(player_center[0] - mini_x, player_center[1] - mini_y) < shockwave_radius + purple_mini_size // 2:
                            spawn_death_effect(mini_x, mini_y, "purple_mini")
                            purple_mini_circles[j].pop(k)
                # Kill purple enemies inside shockwave (only once all their mini circles are gone)
                for i in reversed(range(len(purple_enemies))):
                    if purple_mini_circles[i]:
                        continue
                    ex, ey = purple_enemies[i]
                    enemy_center = (ex + player_size // 2, ey + player_size // 2)
                    if math.hypot(player_center[0] - enemy_center[0], player_center[1] - enemy_center[1]) < shockwave_radius + player_size // 2:
                        remove_purple(i)
                        enemy_killed(ex, ey, "purple")
                        kills += 1

            collect_new_shots()
            bullets_to_remove = []
            for i, bullet in enumerate(bullets):
                bullet["x"] += bullet["dx"]
                bullet["y"] += bullet["dy"]

                # Check if bullet hits barrier boundaries (disabled in storm survival)
                if not in_storm_survival:
                    barrier_thickness = 12
                    if (bullet["x"] < barrier_thickness or 
                        bullet["x"] > MAP_WIDTH - barrier_thickness - bullet_size or
                        bullet["y"] < barrier_thickness or 
                        bullet["y"] > MAP_HEIGHT - barrier_thickness - bullet_size):
                        bullets_to_remove.append(i)
                        continue

                # Check if bullet is too far from player (world coordinates)
                if bullet.get("owner"):
                    bullet["age"] += 1
                    bullet_distance = WIDTH * 3 if bullet["age"] > 150 else 0
                else:
                    bullet_distance = math.hypot(bullet["x"] - player_x, bullet["y"] - player_y)
                if bullet_distance > WIDTH * 2:  # Remove bullets that are too far away
                    bullets_to_remove.append(i)
                    continue

                # Check red enemy hits
                for j, (ex, ey) in enumerate(red_enemies):
                    enemy_rect = pygame.Rect(ex, ey, player_size, player_size)
                    bullet_rect = pygame.Rect(bullet["x"], bullet["y"], bullet_size, bullet_size)
                    if bullet_rect.colliderect(enemy_rect):
                        bullets_to_remove.append(i)
                        # Spawn coin if not shooting range
                        enemy_killed(ex, ey, "red")
                        kills += 1
                        red_enemies.pop(j)
                        break

                # Check green enemy hits
                for j, (ex, ey) in enumerate(green_enemies):
                    enemy_rect = pygame.Rect(ex, ey, player_size, player_size)
                    bullet_rect = pygame.Rect(bullet["x"], bullet["y"], bullet_size, bullet_size)
                    if bullet_rect.colliderect(enemy_rect):
                        bullets_to_remove.append(i)
                        enemy_killed(ex, ey, "green")
                        kills += 1
                        green_enemies.pop(j)
                        break

                # Check purple enemy hits (all 4 mini circles must be destroyed before the big purple can be hit)
                bullet_rect = pygame.Rect(bullet["x"], bullet["y"], bullet_size, bullet_size)
                hit_purple = False
                for j, (ex, ey) in enumerate(purple_enemies):
                    for k, (mini_x, mini_y, _) in enumerate(purple_mini_circles[j]):
                        mini_rect = pygame.Rect(mini_x - purple_mini_size // 2, mini_y - purple_mini_size // 2, purple_mini_size, purple_mini_size)
                        if bullet_rect.colliderect(mini_rect):
                            bullets_to_remove.append(i)
                            spawn_death_effect(mini_x, mini_y, "purple_mini")
                            purple_mini_circles[j].pop(k)
                            hit_purple = True
                            break
                    if hit_purple:
                        break
                    if not purple_mini_circles[j]:
                        enemy_rect = pygame.Rect(ex, ey, player_size, player_size)
                        if bullet_rect.colliderect(enemy_rect):
                            bullets_to_remove.append(i)
                            enemy_killed(ex, ey, "purple")
                            kills += 1
                            remove_purple(j)
                            break

            # Bosses take one damage per shot
            for i, bullet in enumerate(bullets):
                if i not in bullets_to_remove and boss_take_bullet(bullet):
                    bullets_to_remove.append(i)

            # Orange laser enemies can be shot too
            for i, bullet in enumerate(bullets):
                if i in bullets_to_remove:
                    continue
                bullet_rect = pygame.Rect(bullet["x"], bullet["y"], bullet_size, bullet_size)
                for enemy in orange_enemies:
                    if bullet_rect.colliderect(pygame.Rect(enemy["x"], enemy["y"], player_size, player_size)):
                        bullets_to_remove.append(i)
                        orange_enemies.remove(enemy)
                        enemy_killed(enemy["x"], enemy["y"], "orange")
                        kills += 1
                        break
                else:
                    if teal_hit(bullet_rect) or pink_hit(bullet_rect) or violet_hit(bullet_rect) or yellow_catches(bullet_rect):  # Hit a teal or a yellow's body
                        bullets_to_remove.append(i)

            # Player shots and enemy shots (blue's and yellow's red lasers) break each other when they meet.
            # Checked over the whole frame of movement so fast shots can't slip past each other.
            broken_enemy_shots = set()
            for i, bullet in enumerate(bullets):
                if i in bullets_to_remove:
                    continue
                for j, enemy_shot in enumerate(blue_bullets):
                    if j in broken_enemy_shots:
                        continue
                    rx = (bullet["x"] + bullet_size / 2) - (enemy_shot["x"] + shot_size(enemy_shot) / 2)
                    ry = (bullet["y"] + bullet_size / 2) - (enemy_shot["y"] + shot_size(enemy_shot) / 2)
                    vx, vy = bullet["dx"] - enemy_shot["dx"], bullet["dy"] - enemy_shot["dy"]
                    speed_sq = vx * vx + vy * vy
                    back = 0.0 if speed_sq == 0 else max(0.0, min(1.0, (rx * vx + ry * vy) / speed_sq))
                    if math.hypot(rx - vx * back, ry - vy * back) < (bullet_size + shot_size(enemy_shot)) / 2 + 6:
                        bullets_to_remove.append(i)
                        if not enemy_shot.get("tough"):  # Boss orbs stop your shot but don't break
                            broken_enemy_shots.add(j)
                        spawn_shot_clash(bullet["x"] + bullet_size / 2, bullet["y"] + bullet_size / 2)
                        break
            for j in sorted(broken_enemy_shots, reverse=True):
                blue_bullets.pop(j)

            # A bullet can be marked more than once (e.g. touching two enemies), so only remove it once
            for i in sorted(set(bullets_to_remove), reverse=True):
                bullets.pop(i)

            # Coin pickup logic
            if not in_shooting_range:  # Coins drop and can be collected in every mode except the Sandbox
                for coin in coins[:]:
                    update_coin_bounce(coin)
                    dist = math.hypot(player_x + player_size//2 - coin["x"], player_y + player_size//2 - coin["y"])
                    # Magnet effect
                    magnet_range = MAGNET_RANGES[magnet_level()]
                    
                    if magnet_range > 0 and dist < magnet_range:
                        # Move coin toward player
                        dx = player_x + player_size//2 - coin["x"]
                        dy = player_y + player_size//2 - coin["y"]
                        move_dist = min(8, dist)  # max speed
                        if dist > 0:
                            coin["x"] += dx / dist * move_dist
                            coin["y"] += dy / dist * move_dist
                    # Collect coin if close enough
                    if dist < player_size:
                        coins.remove(coin)
                        coin_count += 1
                        sounds.play("coin", 0.7)
                        # Update the appropriate coin variable based on game mode
                        if in_block_defence:
                            block_defence_coins = coin_count
                            main_game_coins += 1  # Block Defence coins are yours to keep too
                        else:
                            main_game_coins = coin_count  # Update main game coins
            else:
                coins.clear()

            # Check enemy/player collisions for game over
            player_rect = pygame.Rect(player_x - camera_x, player_y - camera_y, player_size, player_size)
            if not player_safe():
                for ex, ey in red_enemies:
                    enemy_rect = pygame.Rect(ex - camera_x, ey - camera_y, player_size, player_size)
                    if enemy_rect.colliderect(player_rect):
                        game_over = True
                        # Reset Block Defence coins when player dies
                        if in_block_defence:
                            block_defence_coins = 0
                            block_health = 50
                        # Clear cooldowns when player dies
                        shield_cooldown = 0.0
                        teleport_cooldown = 0.0
                        freeze_cooldown = 0.0
                        freeze_active = False
                        freeze_timer = 0.0
                for ex, ey in green_enemies:
                    enemy_rect = pygame.Rect(ex - camera_x, ey - camera_y, player_size, player_size)
                    if enemy_rect.colliderect(player_rect):
                        game_over = True
                        # Reset Block Defence coins when player dies
                        if in_block_defence:
                            block_defence_coins = 0
                        # Clear cooldowns when player dies
                        shield_cooldown = 0.0
                        teleport_cooldown = 0.0
                        freeze_cooldown = 0.0
                        freeze_active = False
                        freeze_timer = 0.0
                for j, (ex, ey) in enumerate(purple_enemies):
                    enemy_rect = pygame.Rect(ex - camera_x, ey - camera_y, player_size, player_size)
                    purple_hit = enemy_rect.colliderect(player_rect)  # Only the big purple kills; its minis are harmless
                    if purple_hit:
                        game_over = True
                        # Reset Block Defence coins when player dies
                        if in_block_defence:
                            block_defence_coins = 0
                        # Clear cooldowns when player dies
                        shield_cooldown = 0.0
                        teleport_cooldown = 0.0
                        freeze_cooldown = 0.0
                        freeze_active = False
                        freeze_timer = 0.0
            for ex, ey in blue_enemies:
                enemy_rect = pygame.Rect(ex - camera_x, ey - camera_y, player_size, player_size)
                if not player_safe() and enemy_rect.colliderect(player_rect):
                    game_over = True
                    # Reset Block Defence coins when player dies
                    if in_block_defence:
                        block_defence_coins = 0
                    # Clear cooldowns when player dies
                    shield_cooldown = 0.0
                    teleport_cooldown = 0.0
                    freeze_cooldown = 0.0
                    freeze_active = False
                    freeze_timer = 0.0
                    blue_bullets_to_remove.append(i)
            
            # Block Defence: Check red enemy collision with block
            if in_block_defence:
                block_rect = pygame.Rect(BLOCK_DEFENCE_BLOCK_RECT.x - camera_x, BLOCK_DEFENCE_BLOCK_RECT.y - camera_y, BLOCK_DEFENCE_BLOCK_RECT.width, BLOCK_DEFENCE_BLOCK_RECT.height)
                for kind, group in (("red", red_enemies), ("green", green_enemies), ("blue", blue_enemies), ("purple", purple_enemies)):
                    for i in reversed(range(len(group))):
                        ex, ey = group[i]
                        enemy_rect = pygame.Rect(ex - camera_x, ey - camera_y, player_size, player_size)
                        if enemy_rect.colliderect(block_rect):
                            damage_block(1)
                            spawn_death_effect(ex + player_size // 2, ey + player_size // 2, kind)  # Bursts on impact
                            if kind == "purple":
                                for mini_x, mini_y, _ in purple_mini_circles[i]:
                                    spawn_death_effect(mini_x, mini_y, "purple_mini")
                                remove_purple(i)
                            else:
                                group.pop(i)
                                if kind == "blue" and i < len(blue_last_shot_times):
                                    blue_last_shot_times.pop(i)
        # Orange laser enemies (not in the Sandbox editor, and not while paused)
        if not game_paused and not (in_shooting_range and shooting_range_editor_mode):
            update_orange_enemies(dt)
            update_yellow_enemies(dt)
            update_teal_enemies(dt)
            update_pink_enemies(dt)
            update_violet_enemies(dt)
            update_boss(dt)
            if not game_over and not player_safe():
                for enemy in yellow_enemies:
                    if math.hypot(enemy["x"] - player_x, enemy["y"] - player_y) < player_size:
                        player_hit()
                        break
        # Blue enemy logic (all blue enemies)
        blue_bullets_to_remove = []
        player_rect = pygame.Rect(player_x - camera_x, player_y - camera_y, player_size, player_size)
        for idx, (ex, ey) in enumerate(blue_enemies):
            # Only move blue enemies if not paused, freeze is not active and not in editor mode
            if not game_paused and not (has_freeze and equipped_ability == 'freeze' and freeze_active) and not (in_shooting_range and shooting_range_editor_mode):
                target_x, target_y = enemy_target(ex, ey)
                dx = target_x - ex
                dy = target_y - ey
                dist = math.hypot(dx, dy)
                if dist != 0:
                    dx /= dist
                    dy /= dist
                    ex += dx * blue_enemy_speed
                    ey += dy * blue_enemy_speed
                blue_enemies[idx] = [ex, ey]
            # Blue enemy shooting (also stopped while paused, frozen or in editor mode)
            if not game_paused and not (has_freeze and equipped_ability == 'freeze' and freeze_active) and not (in_shooting_range and shooting_range_editor_mode):
                now = pygame.time.get_ticks() / 1000
                while len(blue_last_shot_times) <= idx:
                    blue_last_shot_times.append(now)
                aim_x, aim_y = enemy_target(ex, ey)
                in_range = math.hypot(aim_x - ex, aim_y - ey) <= BLUE_SHOOT_RANGE
                if in_range and now - blue_last_shot_times[idx] >= blue_shot_delay:
                    bx = ex + player_size // 2
                    by = ey + player_size // 2
                    pdx = aim_x + player_size // 2 - bx
                    pdy = aim_y + player_size // 2 - by
                    pdist = math.hypot(pdx, pdy)
                    if pdist != 0:
                        pdx /= pdist
                        pdy /= pdist
                    blue_bullets.append({"x": bx, "y": by, "dx": pdx * blue_bullet_speed, "dy": pdy * blue_bullet_speed})
                    blue_last_shot_times[idx] = now
        # Blue bullet movement (stopped while paused and in editor mode)
        if not game_paused and not (in_shooting_range and shooting_range_editor_mode):
            for i, b in enumerate(blue_bullets):
                if b.get("orb"):
                    curve_flung_orb(b, dt)
                b["x"] += b["dx"]
                b["y"] += b["dy"]
        
        # Blue bullet collision detection (always active)
        for i, b in enumerate(blue_bullets):
            # Check if bullet hits barrier boundaries (disabled in storm survival)
            if not in_storm_survival:
                barrier_thickness = 12
                hit_x = b["x"] < barrier_thickness or b["x"] > MAP_WIDTH - barrier_thickness - shot_size(b)
                hit_y = b["y"] < barrier_thickness or b["y"] > MAP_HEIGHT - barrier_thickness - shot_size(b)
                if (hit_x or hit_y) and b.get("bounces", 0) > 0:
                    # Bouncing orbs flip direction off the barrier and use up one bounce
                    if hit_x:
                        b["dx"] = -b["dx"]
                        b["x"] = max(barrier_thickness, min(MAP_WIDTH - barrier_thickness - shot_size(b), b["x"]))
                    if hit_y:
                        b["dy"] = -b["dy"]
                        b["y"] = max(barrier_thickness, min(MAP_HEIGHT - barrier_thickness - shot_size(b), b["y"]))
                    b["bounces"] -= 1
                elif hit_x or hit_y:
                    blue_bullets_to_remove.append(i)
                    continue

            # Check if bullet is too far from player (world coordinates)
            near_x, near_y = nearest_player(b["x"], b["y"]) if multiplayer_match else (player_x, player_y)
            bullet_distance = math.hypot(b["x"] - near_x, b["y"] - near_y)
            if bullet_distance > WIDTH * 2 and "bounces" not in b:  # Remove bullets that are too far away
                blue_bullets_to_remove.append(i)
                continue
            if in_block_defence and BLOCK_DEFENCE_BLOCK_RECT.colliderect(pygame.Rect(b["x"], b["y"], shot_size(b), shot_size(b))):
                damage_block(1)  # Each shot that reaches the block does 1 damage
                blue_bullets_to_remove.append(i)
                continue
            bullet_rect = pygame.Rect(b["x"] - camera_x, b["y"] - camera_y, shot_size(b), shot_size(b))
            if not player_safe() and bullet_rect.colliderect(player_rect):
                game_over = True
                # Reset Block Defence coins when player dies
                if in_block_defence:
                    block_defence_coins = 0
                # Clear cooldowns when player dies
                shield_cooldown = 0.0
                teleport_cooldown = 0.0
                freeze_cooldown = 0.0
                freeze_active = False
                freeze_timer = 0.0
                blue_bullets_to_remove.append(i)
        for i in reversed(blue_bullets_to_remove):
            blue_bullets.pop(i)
        # Player bullet vs blue enemies
        player_bullets_to_remove = []
        blue_enemies_to_remove = []
        for idx, (ex, ey) in enumerate(blue_enemies):
            blue_enemy_rect = pygame.Rect(ex - camera_x, ey - camera_y, player_size, player_size)
            for i, bullet in enumerate(bullets):
                if i in player_bullets_to_remove:
                    continue  # This shot already killed a blue; one shot, one kill (and no double removal crash)
                bullet_rect = pygame.Rect(bullet["x"] - camera_x, bullet["y"] - camera_y, bullet_size, bullet_size)
                if bullet_rect.colliderect(blue_enemy_rect):
                    player_bullets_to_remove.append(i)
                    blue_enemies_to_remove.append(idx)
                    enemy_killed(ex, ey, "blue")
                    kills += 1
                    break
        for i in sorted(set(player_bullets_to_remove), reverse=True):  # Highest first so the others don't shift
            bullets.pop(i)
        for idx in reversed(blue_enemies_to_remove):
            blue_enemies.pop(idx)
            if blue_last_shot_times and idx < len(blue_last_shot_times):
                blue_last_shot_times.pop(idx)
            max_blue_enemies = max(0, max_blue_enemies - 1)

        # Draw everything (always visible, even when paused)
        # Update player and mini colors for rainbow skin
        if current_skin == "rainbow":
            elapsed = pygame.time.get_ticks() / 1000.0
            player_color = rainbow_color_cycle(elapsed, 2.0)
            mini_color = player_color
        else:
            player_color = skin_colors.get(current_skin, WHITE)
            mini_color = player_color

        # Draw the player as a beveled 3D cube (skin texture or color) with a visor aimed at the mouse
        if current_skin in SKIN_TEXTURES and owned_skins[current_skin]:
            player_face = SKIN_TEXTURES[current_skin]
        else:
            player_face = player_color
        if not game_over:  # On the frame the player dies they shatter instead (see the death snapshot further down)
            draw_player_cube(player_x - camera_x, player_y - camera_y, player_face, SKIN_GLOWS.get(current_skin, player_color), last_rot_angle)
        if multiplayer_match:
            draw_remote_players()
        
        # Draw Block Defence block
        if in_block_defence:
            draw_block_defence_block()
        
        # Shield held out on the gun side
        if has_shield and equipped_ability == 'shield' and shield_active:
            draw_shield()
        
        # Draw shockwave: an expanding blast ring with a white-hot edge, trailing rings and energy spokes
        if has_shockwave and equipped_ability == 'shockwave' and shockwave_active:
            player_center = (player_x - camera_x + player_size // 2, player_y - camera_y + player_size // 2)
            progress = min(1.0, shockwave_timer / shockwave_duration)
            fade = 1 - progress
            shockwave_surface = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
            # Soft blast filling the ring, thinning out as it spreads
            pygame.draw.circle(shockwave_surface, (170, 40, 255, int(95 * fade)), player_center, shockwave_radius)
            # Trailing rings, so it reads as a pulse instead of a growing disc
            for trail, alpha in ((0.78, 130), (0.55, 80)):
                trail_radius = int(shockwave_radius * trail)
                if trail_radius > 4:
                    pygame.draw.circle(shockwave_surface, (170, 70, 255, int(alpha * fade)), player_center,
                                       trail_radius, max(2, int(8 * fade)))
            # Energy spokes shooting out through the leading edge
            for spoke in range(12):
                angle = spoke * math.pi / 6 + shockwave_timer * 2
                inner = shockwave_radius * 0.72
                pygame.draw.line(shockwave_surface, (240, 190, 255, int(210 * fade)),
                                 (player_center[0] + math.cos(angle) * inner, player_center[1] + math.sin(angle) * inner),
                                 (player_center[0] + math.cos(angle) * shockwave_radius, player_center[1] + math.sin(angle) * shockwave_radius), 4)
            # Leading edge: thick glow with a white-hot core
            edge = max(2, int(18 * fade) + 2)
            pygame.draw.circle(shockwave_surface, (205, 110, 255, int(195 * fade)), player_center, shockwave_radius, edge)
            pygame.draw.circle(shockwave_surface, (255, 235, 255, int(255 * fade)), player_center, shockwave_radius, max(3, edge // 2))
            screen.blit(shockwave_surface, (0, 0))

        # Ability cooldown/duration badge at the top middle
        draw_ability_badge(dt)

        # Shield collision logic
        if has_shield and equipped_ability == 'shield' and shield_active:
            # Red enemies
            for i in reversed(range(len(red_enemies))):
                ex, ey = red_enemies[i]
                enemy_center = (ex + player_size // 2, ey + player_size // 2)
                if shield_blocks(enemy_center[0], enemy_center[1], player_size // 2):
                    enemy_killed(ex, ey, "red")
                    red_enemies.pop(i)
                    max_red_enemies = max(0, max_red_enemies - 1)
                    kills += 1
            # Green enemies
            for i in reversed(range(len(green_enemies))):
                ex, ey = green_enemies[i]
                enemy_center = (ex + player_size // 2, ey + player_size // 2)
                if shield_blocks(enemy_center[0], enemy_center[1], player_size // 2):
                    enemy_killed(ex, ey, "green")
                    green_enemies.pop(i)
                    max_green_enemies = max(0, max_green_enemies - 1)
                    kills += 1
            # Blue enemies
            for i in reversed(range(len(blue_enemies))):
                ex, ey = blue_enemies[i]
                enemy_center = (ex + player_size // 2, ey + player_size // 2)
                if shield_blocks(enemy_center[0], enemy_center[1], player_size // 2):
                    enemy_killed(ex, ey, "blue")
                    blue_enemies.pop(i)
                    if i < len(blue_last_shot_times):
                        blue_last_shot_times.pop(i)
                    max_blue_enemies = max(0, max_blue_enemies - 1)
                    kills += 1
            # Blue bullets
            for i in reversed(range(len(blue_bullets))):
                b = blue_bullets[i]
                if shield_blocks(b["x"] + shot_size(b) / 2, b["y"] + shot_size(b) / 2, shot_size(b) / 2):
                    blue_bullets.pop(i)
            
            # Orange and yellow enemies
            for kind, group in dict_enemy_groups():
                for enemy in group[:]:
                    if shield_blocks(enemy["x"] + player_size // 2, enemy["y"] + player_size // 2, player_size // 2):
                        group.remove(enemy)
                        enemy_killed(enemy["x"], enemy["y"], kind)
                        kills += 1
            # Purple mini circles
            for j in range(len(purple_enemies)):
                for k in reversed(range(len(purple_mini_circles[j]))):
                    mini_x, mini_y, _ = purple_mini_circles[j][k]
                    if shield_blocks(mini_x, mini_y, purple_mini_size // 2):
                        spawn_death_effect(mini_x, mini_y, "purple_mini")
                        purple_mini_circles[j].pop(k)
            # Purple enemies (only once all their mini circles are gone)
            for i in reversed(range(len(purple_enemies))):
                if purple_mini_circles[i]:
                    continue
                ex, ey = purple_enemies[i]
                enemy_center = (ex + player_size // 2, ey + player_size // 2)
                if shield_blocks(enemy_center[0], enemy_center[1], player_size // 2):
                    enemy_killed(ex, ey, "purple")
                    remove_purple(i)
                    max_purple_enemies = max(0, max_purple_enemies - 1)
                    kills += 1

        # Plasma lasers: blue for the player (and helpers), red for blue enemies.
        # Drawn before the enemies so a freshly fired bolt comes out from under its shooter.
        for bullet in bullets:
            draw_laser("player", bullet["x"] - camera_x + bullet_size / 2, bullet["y"] - camera_y + bullet_size / 2, bullet["dx"], bullet["dy"])
        for b in blue_bullets:
            if b.get("orb"):
                ox, oy = b["x"] - camera_x + shot_size(b) / 2, b["y"] - camera_y + shot_size(b) / 2
                if on_screen(ox, oy, 60):
                    draw_flung_orb(ox, oy, pygame.time.get_ticks() / 1000, radius=int(shot_size(b) / 2), color=b.get("orb_color", "red"))
                continue
            draw_laser("enemy", b["x"] - camera_x + shot_size(b) / 2, b["y"] - camera_y + shot_size(b) / 2, b["dx"], b["dy"], b.get("scale", 1))

        # Draw enemies as shaded orbs with ground shadows and an eye that watches the player
        half = player_size // 2
        look_x, look_y = enemy_target()[0] - camera_x + half, enemy_target()[1] - camera_y + half
        for ex, ey in red_enemies:
            cx, cy = ex - camera_x + half, ey - camera_y + half
            if not on_screen(cx, cy):
                continue
            draw_orb(red_orb, enemy_shadow, cx, cy)
            draw_eye(cx, cy, look_x, look_y, 8, half * 0.3)

        # Green enemies are fast, so they leave a short speed trail behind them
        for ex, ey in green_enemies:
            cx, cy = ex - camera_x + half, ey - camera_y + half
            if not on_screen(cx, cy, 120):  # Extra margin for the speed trail
                continue
            dx, dy = player_x - ex, player_y - ey
            dist = math.hypot(dx, dy) or 1
            for k in reversed(range(len(green_trail))):
                back = (k + 1) * 11
                ghost = green_trail[k]
                screen.blit(ghost, (cx - dx / dist * back - ghost.get_width() // 2, cy - dy / dist * back - ghost.get_height() // 2))
            draw_orb(green_orb, enemy_shadow, cx, cy)
            draw_eye(cx, cy, look_x, look_y, 8, half * 0.3)

        # Purple enemies: glowing energy tethers to their mini orbs
        for j, (ex, ey) in enumerate(purple_enemies):
            center = (ex - camera_x + half, ey - camera_y + half)
            if not on_screen(*center, 150):  # Extra margin for its minis
                continue
            minis_on_screen = [(mini_x - camera_x, mini_y - camera_y) for mini_x, mini_y, _ in purple_mini_circles[j]]
            for mini_center in minis_on_screen:
                pygame.draw.line(screen, (90, 30, 140), center, mini_center, 6)
                pygame.draw.line(screen, (225, 160, 255), center, mini_center, 2)
            draw_orb(purple_orb, enemy_shadow, *center)
            draw_eye(*center, look_x, look_y, 9, half * 0.3)
            # Shield ring while any minis are alive (the big purple can't be hurt yet)
            if minis_on_screen:
                pygame.draw.circle(screen, (215, 160, 255), center, half + 6, 2)
            for mini_center in minis_on_screen:
                draw_orb(purple_mini_orb, mini_shadow, *mini_center)
                draw_eye(*mini_center, look_x, look_y, 3, 1.5)

        # Blue enemies: a gun barrel and sensor eye that aim at the player (the block in Block Defence)
        for idx, (ex, ey) in enumerate(blue_enemies):
            cx, cy = ex - camera_x + half, ey - camera_y + half
            if not on_screen(cx, cy):
                continue
            dx, dy = enemy_target()[0] - ex, enemy_target()[1] - ey
            dist = math.hypot(dx, dy) or 1
            dx, dy = dx / dist, dy / dist
            draw_shadow(enemy_shadow, cx, cy)
            barrel_end = (cx + dx * (half + 16), cy + dy * (half + 16))
            pygame.draw.line(screen, (35, 38, 48), (cx, cy), barrel_end, 12)
            pygame.draw.line(screen, (110, 120, 140), (cx, cy), barrel_end, 4)
            draw_orb(blue_orb, None, cx, cy)
            draw_eye(cx, cy, look_x, look_y, 8, half * 0.45)
            if idx < len(blue_last_shot_times):
                draw_muzzle_flash(*barrel_end, (255, 90, 80), pygame.time.get_ticks() / 1000 - blue_last_shot_times[idx])

        draw_orange_enemies()
        draw_yellow_enemies()
        draw_teal_enemies()
        draw_violet_enemies()  # Under the others, since its swirl covers a big area
        draw_pink_enemies()
        draw_boss()
        if active_boss is not None:
            draw_orange_lines(active_boss)

        # Death effects: shards and flashes from defeated enemies
        update_and_draw_effects(dt, game_paused)

        # Freeze: enemies locked in ice, and the whole screen frosted over
        if has_freeze and equipped_ability == 'freeze' and freeze_active:
            draw_frozen_world()

        # Helpers movement, shooting, and drawing
        if helpers_active:
            for helper in helpers:
                # Find closest enemy to this helper
                helper_center_x = helper["x"] + helper_size // 2
                helper_center_y = helper["y"] + helper_size // 2
                closest_enemy = None
                closest_distance = float('inf')
                
                # Check all enemy types
                for enemy in red_enemies + green_enemies + blue_enemies + purple_enemies:
                    enemy_center_x = enemy[0] + player_size // 2
                    enemy_center_y = enemy[1] + player_size // 2
                    distance = math.hypot(helper_center_x - enemy_center_x, helper_center_y - enemy_center_y)
                    if distance < closest_distance:
                        closest_distance = distance
                        closest_enemy = enemy
                
                if closest_enemy:
                    # Move towards closest enemy
                    enemy_center_x = closest_enemy[0] + player_size // 2
                    enemy_center_y = closest_enemy[1] + player_size // 2
                    dx = enemy_center_x - helper_center_x
                    dy = enemy_center_y - helper_center_y
                    distance = math.hypot(dx, dy)
                    if distance > 0:
                        dx = (dx / distance) * helper_speed
                        dy = (dy / distance) * helper_speed
                        helper["x"] += dx
                        helper["y"] += dy
                    
                    # Update helper angle to face enemy
                    helper["angle"] = math.atan2(dy, dx)
                    
                    # Shoot at enemy if close enough and cooldown is ready
                    current_time = pygame.time.get_ticks() / 1000
                    if distance < 200 and current_time - helper["last_shot_time"] >= shot_delay:
                        # Create helper bullet
                        bullet_speed = 8
                        bullet_dx = math.cos(helper["angle"]) * bullet_speed
                        bullet_dy = math.sin(helper["angle"]) * bullet_speed
                        bullets.append({
                            "x": helper_center_x,
                            "y": helper_center_y,
                            "dx": bullet_dx,
                            "dy": bullet_dy,
                            "is_helper_bullet": True  # Mark as helper bullet
                        })
                        helper["last_shot_time"] = current_time
                
                # Helpers are little versions of the player cube, in the same skin, with their visor
                # pointing at whatever they are shooting at
                helper_skin = helper["skin"]
                helper_face = skin_face(helper_skin, pygame.time.get_ticks() / 1000.0)
                helper_glow = SKIN_GLOWS.get(helper_skin, helper_face if isinstance(helper_face, tuple) else WHITE)
                draw_player_cube(helper["x"] - camera_x, helper["y"] - camera_y, helper_face, helper_glow,
                                 helper["angle"], size=helper_size)

        # Draw the orbiting mini gun: a barrel pointing where you aim, under a round gun body
        # (skipped on the frame the player dies, so it isn't frozen into the death snapshot)
        if not game_over:
            mini_center = (orbit_x - camera_x + mini_size // 2, orbit_y - camera_y + mini_size // 2)
            barrel_end = (mini_center[0] + math.cos(last_rot_angle) * 16, mini_center[1] + math.sin(last_rot_angle) * 16)
            pygame.draw.line(screen, (30, 32, 40), mini_center, barrel_end, 8)
            pygame.draw.line(screen, (150, 155, 170), mini_center, barrel_end, 3)
            if current_skin in SKIN_TEXTURES and owned_skins[current_skin]:
                # Textured skins: the texture in a soft glow, turned to face the aim direction
                mini_surface = pygame.Surface((mini_size + 6, mini_size + 6), pygame.SRCALPHA)
                pygame.draw.circle(mini_surface, (*SKIN_GLOWS[current_skin], 60), (mini_size // 2 + 3, mini_size // 2 + 3), mini_size // 2 + 3)
                mini_surface.blit(pygame.transform.smoothscale(SKIN_TEXTURES[current_skin], (mini_size, mini_size)), (3, 3))
                rotated_mini = pygame.transform.rotate(mini_surface, -math.degrees(last_rot_angle))
                screen.blit(rotated_mini, rotated_mini.get_rect(center=mini_center))
            else:
                # Color skins: a small shaded orb in the skin color
                draw_orb(create_orb_sprite(mini_color[:3], mini_size // 2, glow=4), None, *mini_center)
            draw_muzzle_flash(*barrel_end, (120, 200, 255), pygame.time.get_ticks() / 1000 - last_shot_time)

        # Draw coins: golden orbs with a ground shadow (freshly dropped coins hop above their shadow)
        for coin in coins:
            coin_x, coin_y = coin["x"] - camera_x, coin["y"] - camera_y
            if not on_screen(coin_x, coin_y, 40):
                continue
            draw_shadow(coin_shadow, coin_x, coin_y)
            draw_orb(coin_orb, None, coin_x, coin_y - coin.get("z", 0))

        # The moment the player dies: remember the world (no HUD, no player) so the game-over
        # screen can slowly zoom out from it, and shatter the player
        if game_over and death_snapshot is None:
            death_snapshot = screen.copy()
            death_time = pygame.time.get_ticks() / 1000
            effects.clear()  # Enemy bursts already in flight are frozen into the snapshot
            spawn_death_effect(player_x + player_size / 2, player_y + player_size / 2, "player", SKIN_GLOWS.get(current_skin, player_color))

        # In-game buttons and minimap (drawn after the death snapshot so they aren't frozen into the game-over screen)
        draw_game_buttons()
        draw_minimap()
        if in_tutorial:
            draw_tutorial_banner()

        # Kills, coins and time in one bar under the minimap
        stats = [("kills", str(kills), WHITE)]
        if not in_shooting_range:  # No coins in the Sandbox
            # Your total coins (the Tutorial shows its practice coins instead)
            stats.append(("coins", str(coin_count if in_tutorial else main_game_coins), (255, 222, 95)))
        # Enemy counter (Waves, Barrier Shrink and Block Defence); a boss counts as one
        enemy_count = (len(red_enemies) + len(green_enemies) + len(blue_enemies) + len(purple_enemies)
                       + len(orange_enemies) + len(yellow_enemies) + len(teal_enemies) + len(pink_enemies) + len(violet_enemies) + (1 if active_boss is not None else 0))
        enemy_stat = ("enemies", str(enemy_count), (255, 140, 130))
        if in_block_defence:
            time_left = max(0, 301 - game_timer)  # 5-minute countdown that starts at 5:00
            stats.append(("time", f"{int(time_left // 60):02d}:{int(time_left % 60):02d}", RED if time_left <= 0 else WHITE))
            stats.append(enemy_stat)
            stats.append(("points", f"P: {block_defence_points}", (120, 220, 255)))
        elif in_storm_survival:
            draw_storm_timer(max(0, math.ceil(180 - game_timer)))  # Barrier Shrink shows its time in the tab up top
            stats.append(enemy_stat)
        else:
            stats.append(("time", f"{int(game_timer // 60):02d}:{int(game_timer % 60):02d}", WHITE))
            if not in_shooting_range and not in_tutorial:  # Waves
                stats.append(enemy_stat)
        draw_stats_bar(stats)
        draw_boss_health()

        # Draw wave top left (hide wave in shooting range, storm survival, and block defence)
        if not in_shooting_range and not in_storm_survival and not in_block_defence and not in_tutorial:
            wave_text = coin_font.render(f"Wave {wave}", True, WHITE)
            blit_hud(wave_text, (20, 20))
        elif in_storm_survival:
            # Draw win message if player has won
            if storm_survival_won:
                win_text = font.render("You Win!", True, YELLOW)
                win_rect = win_text.get_rect(center=(WIDTH // 2, 150))  # Below the timer tab
                blit_hud(win_text, win_rect)
        elif in_block_defence:
            # Show "You Lose!" text when block health reaches 0
            if block_health <= 0:
                lose_text = font.render("You Lose!", True, RED)
                lose_rect = lose_text.get_rect(center=(WIDTH // 2, 40))
                screen.blit(lose_text, lose_rect)
        
        # Wave complete banner: drops in from the top, hangs there, then flies back up
        if wave_completion_timer > 0:
            banner = get_bubble_text(wave_completion_message, 72, (255, 240, 120), (255, 150, 30))
            reward = get_bubble_text(f"+{wave_completion_reward} Coins", 40, (255, 250, 200), (255, 200, 40), outline=6)
            shown_for = wave_completion_duration - wave_completion_timer
            if shown_for < 0.45:
                slide = ease_out_back(shown_for / 0.45)  # Dropping in
            elif wave_completion_timer < 0.4:
                slide = 1 - ease_in_cubic(1 - wave_completion_timer / 0.4)  # Flying back up
            else:
                slide = 1.0
            hidden_y = -(banner.get_height() + reward.get_height())
            banner_y = hidden_y + (70 - hidden_y) * slide
            screen.blit(banner, (WIDTH // 2 - banner.get_width() // 2, banner_y))
            screen.blit(reward, (WIDTH // 2 - reward.get_width() // 2, banner_y + banner.get_height() - 25))

    elif game_over:
        # Game-over sequence: the frozen world slowly zooms out while the player's pieces fly apart,
        # then GAME OVER drops in from the top and the buttons rise up from the bottom
        since_death = pygame.time.get_ticks() / 1000 - death_time
        if death_snapshot is not None:
            zoom = game_over_zoom()
            zoomed_world = pygame.transform.smoothscale(death_snapshot, (round(WIDTH * zoom), round(HEIGHT * zoom)))
            screen.blit(zoomed_world, zoomed_world.get_rect(center=(WIDTH // 2, HEIGHT // 2)))
            update_and_draw_effects(dt, False, zoom)
            dim = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
            dim.fill((0, 0, 0, int(140 * min(1.0, since_death / 1.2))))
            screen.blit(dim, (0, 0))
        title_t = min(1.0, max(0.0, (since_death - 0.5) / 0.6))
        buttons_t = min(1.0, max(0.0, (since_death - 0.8) / 0.6))
        title_offset = -(1 - ease_out_back(title_t)) * 500  # Slides down from above the screen
        button_offset = (1 - ease_out_back(buttons_t)) * 500  # Rises up from below the screen
        buttons_ready = buttons_t >= 1.0  # Buttons only work once they've landed

        screen.blit(game_over_title, (WIDTH // 2 - game_over_title.get_width() // 2, HEIGHT // 2 - 265 + title_offset))

        # Final stats (they travel with the title)
        minutes = int(game_timer // 60)
        seconds = int(game_timer % 60)
        draw_text_with_shadow(f"Kills: {kills}", button_font, WHITE, (WIDTH // 2, HEIGHT // 2 - 80 + title_offset))
        draw_text_with_shadow(f"Wave: {wave}", button_font, WHITE, (WIDTH // 2, HEIGHT // 2 - 45 + title_offset))
        draw_text_with_shadow(f"Time: {minutes:02d}:{seconds:02d}", button_font, WHITE, (WIDTH // 2, HEIGHT // 2 - 10 + title_offset))

        if in_storm_survival:
            # Center Retry and Menu buttons as a group
            button_width = 150
            button_height = 60
            button_spacing = 40
            total_width = button_width * 2 + button_spacing
            start_x = WIDTH // 2 - total_width // 2
            y = HEIGHT // 2 + 50 + button_offset
            retry_button = pygame.Rect(start_x, y, button_width, button_height)
            menu_button = pygame.Rect(start_x + button_width + button_spacing, y, button_width, button_height)
            draw_button(retry_button, BLUE)
            draw_button(menu_button, BLUE)
            retry_text = button_font.render("Retry", True, BLACK)
            menu_text = button_font.render("Menu", True, BLACK)
            screen.blit(retry_text, (retry_button.x + (button_width - retry_text.get_width()) // 2, retry_button.y + (button_height - retry_text.get_height()) // 2))
            screen.blit(menu_text, (menu_button.x + (button_width - menu_text.get_width()) // 2, menu_button.y + (button_height - menu_text.get_height()) // 2))
        else:
            # Center the buttons with the game over text
            button_width = 150
            button_height = 60
            button_spacing = 40
            
            if in_block_defence:
                # For Block Defence: only Retry and Menu buttons, centered
                total_width = button_width * 2 + button_spacing
                start_x = WIDTH // 2 - total_width // 2
                y = HEIGHT // 2 + 50 + button_offset

                retry_button = pygame.Rect(start_x, y, button_width, button_height)
                menu_button = pygame.Rect(start_x + button_width + button_spacing, y, button_width, button_height)
                
                draw_button(retry_button, BLUE)
                draw_button(menu_button, BLUE)
                
                retry_text = button_font.render("Retry", True, BLACK)
                menu_text = button_font.render("Menu", True, BLACK)
                
                screen.blit(retry_text, (retry_button.x + (button_width - retry_text.get_width()) // 2, retry_button.y + (button_height - retry_text.get_height()) // 2))
                screen.blit(menu_text, (menu_button.x + (button_width - menu_text.get_width()) // 2, menu_button.y + (button_height - menu_text.get_height()) // 2))
            else:
                # For other modes: Retry, Skins, Upgrades, and Menu buttons
                retry_text = button_font.render("Retry", True, BLACK)
                retry_button = pygame.Rect(WIDTH // 2 - 170, HEIGHT // 2 + 40 + button_offset, 150, 60)
                draw_button(retry_button, BLUE)
                screen.blit(retry_text, retry_text.get_rect(center=retry_button.center))

                menu_text = button_font.render("Menu", True, BLACK)
                menu_button = pygame.Rect(WIDTH // 2 + 20, HEIGHT // 2 + 40 + button_offset, 150, 60)
                draw_button(menu_button, BLUE)
                screen.blit(menu_text, menu_text.get_rect(center=menu_button.center))

        # Handle events for the game over buttons
        for event in events:
            if event.type == pygame.MOUSEBUTTONDOWN and not console_open and buttons_ready:
                mx, my = pygame.mouse.get_pos()
                if in_storm_survival:
                    if retry_button.collidepoint(mx, my):
                        reset_game(storm_survival=True)
                        in_storm_survival = True
                        game_over = False
                        start_screen = False
                        game_mode_selection = False
                    if menu_button.collidepoint(mx, my):
                        exit_to_main_menu()  # Leaves the mode properly (puts Sandbox coins back)
                else:
                    if retry_button.collidepoint(mx, my):
                        if in_block_defence:
                            reset_game(block_defence=True)
                            in_block_defence = True
                            game_over = False
                            start_screen = False
                            game_mode_selection = False
                        elif in_shooting_range:
                            retry_sandbox()  # Back into play mode with the enemies you placed
                        else:
                            reset_game(tutorial=in_tutorial)  # Retrying the tutorial restarts the tutorial
                    if menu_button.collidepoint(mx, my):
                        exit_to_main_menu()  # Leaves the mode properly (puts Sandbox coins back)

    # Shield timer/cooldown logic
    if shield_active:
        shield_timer += dt
        if shield_timer >= shield_max_duration:
            shield_active = False
            shield_cooldown = shield_cooldown_time
            shield_timer = 0
    elif shield_cooldown > 0:
        shield_cooldown -= dt
        if shield_cooldown < 0:
            shield_cooldown = 0
            shield_timer = 0

    # Teleport cooldown logic
    if teleport_cooldown > 0:
        teleport_cooldown -= dt
        if teleport_cooldown < 0:
            teleport_cooldown = 0

    # Freeze timer/cooldown logic
    if freeze_active:
        freeze_timer += dt
        if freeze_timer >= freeze_duration:
            freeze_active = False
            freeze_timer = 0
    elif freeze_cooldown > 0:
        freeze_cooldown -= dt
        if freeze_cooldown < 0:
            freeze_cooldown = 0
            freeze_timer = 0

    # Helpers timer/cooldown logic
    if helpers_active:
        helpers_timer += dt
        if helpers_timer >= helpers_duration:
            helpers_active = False
            helpers_timer = 0
            helpers.clear()
    elif helpers_cooldown > 0:
        helpers_cooldown -= dt
        if helpers_cooldown < 0:
            helpers_cooldown = 0

    # Shockwave timer/cooldown logic
    if shockwave_active:
        shockwave_timer += dt
        shockwave_radius = int((shockwave_timer / shockwave_duration) * shockwave_max_radius)
        if shockwave_timer >= shockwave_duration:
            shockwave_active = False
            shockwave_timer = 0
            shockwave_radius = 0
    elif shockwave_cooldown > 0:
        shockwave_cooldown -= dt
        if shockwave_cooldown < 0:
            shockwave_cooldown = 0

    # Game timer logic (only count when not paused and not in menus)
    if (not start_screen and not game_over and not game_paused
            and not hub_open and not settings_open):
        game_timer += dt
        
        # Storm survival enemy spawning and map shrinking
        if in_storm_survival:
            # Win condition: when timer reaches 0, despawn all enemies and stop spawning
            if game_timer >= 180:
                if not storm_survival_won:
                    storm_survival_won = True
                    red_enemies.clear()
                    green_enemies.clear()
                    blue_enemies.clear()
                    blue_last_shot_times.clear()
                    purple_enemies.clear()
                    purple_mini_circles.clear()
                    orange_enemies.clear()
                    yellow_enemies.clear()
                    teal_enemies.clear()
                    pink_enemies.clear()
                    violet_enemies.clear()
                # Prevent further spawning and shrinking
            else:
                storm_survival_won = False
                # Spawn a red enemy every 2 seconds
                red_spawn_interval = 2  # Every 2 seconds for the whole 3 minutes
                if int(game_timer) % red_spawn_interval == 0 and game_timer > 0 and net_role() != "guest":
                    # Only spawn if we haven't already spawned this second
                    if not hasattr(reset_game, 'last_red_spawn_second') or reset_game.last_red_spawn_second != int(game_timer):
                        red_enemies.append(get_safe_enemy_spawn())
                        reset_game.last_red_spawn_second = int(game_timer)
                # Spawn a green or blue every 6 seconds for the first 90 seconds, then every 4 seconds
                green_spawn_interval = 6 if game_timer < 90 else 4
                if int(game_timer) % green_spawn_interval == 0 and game_timer > 0 and net_role() != "guest":
                    # Only spawn if we haven't already spawned this second
                    if not hasattr(reset_game, 'last_green_spawn_second') or reset_game.last_green_spawn_second != int(game_timer):
                        if random.random() < 0.5:  # 50/50 green or blue
                            green_enemies.append(get_safe_enemy_spawn())
                        else:
                            blue_enemies.append(get_safe_enemy_spawn())
                            blue_last_shot_times.append(pygame.time.get_ticks() / 1000)
                        reset_game.last_green_spawn_second = int(game_timer)
                if storm_spawn_due("orange", 10):
                    orange_enemies.append(new_orange_enemy(*get_safe_enemy_spawn()))
                if storm_spawn_due("yellow", 15):
                    yellow_enemies.append(new_yellow_enemy(*get_safe_enemy_spawn()))
                if storm_spawn_due("purple", 30):
                    spawn_purple()
                # Shrink the map over 3 minutes (180 seconds)
                # Start at full size, end at 200x200 pixels
                shrink_progress = min(game_timer / 180.0, 1.0)  # 0 to 1 over 3 minutes
                min_map_size = 200  # Final map size
                # More aggressive shrinking: start at 100%, end at 10% of original size
                current_shrink = 1.0 - (shrink_progress * 0.9)  # Shrink to 10% of original size
                storm_survival_map_width = int(MAP_WIDTH * current_shrink)
                storm_survival_map_height = int(MAP_HEIGHT * current_shrink)
                # Ensure minimum size
                storm_survival_map_width = max(storm_survival_map_width, min_map_size)
                storm_survival_map_height = max(storm_survival_map_height, min_map_size)
                # Debug: Print map size every 10 seconds
                if int(game_timer) % 10 == 0 and game_timer > 0:
                    if not hasattr(reset_game, 'last_debug_second') or reset_game.last_debug_second != int(game_timer):
                        print(f"Storm Survival: {game_timer:.1f}s - Map size: {storm_survival_map_width}x{storm_survival_map_height} (shrink: {current_shrink:.3f})")
                        reset_game.last_debug_second = int(game_timer)
        
        # Block Defence enemy spawning
        elif in_block_defence:
            # Only spawn enemies if block health is above 0
            if block_health > 0:
                # Red every 2 seconds, green every 6, blue every 10, purple every 30, orange every 45
                if storm_spawn_due("bd_red", 2):
                    red_enemies.append(get_safe_enemy_spawn())
                if storm_spawn_due("bd_green", 6):
                    green_enemies.append(get_safe_enemy_spawn())
                if storm_spawn_due("bd_blue", 10):
                    blue_enemies.append(get_safe_enemy_spawn())
                    blue_last_shot_times.append(pygame.time.get_ticks() / 1000)
                if storm_spawn_due("bd_purple", 30):
                    spawn_purple()
                if storm_spawn_due("bd_orange", 45):
                    orange_enemies.append(new_orange_enemy(*get_safe_enemy_spawn()))
            else:
                # Block health is 0, despawn all enemies
                red_enemies.clear()
                green_enemies.clear()
                blue_enemies.clear()
                blue_last_shot_times.clear()
                blue_bullets.clear()
                purple_enemies.clear()
                purple_mini_circles.clear()
                orange_enemies.clear()
                yellow_enemies.clear()
                teal_enemies.clear()
                pink_enemies.clear()
                violet_enemies.clear()
                
                # Start game over timer if not already started
                if block_defence_game_over_timer == 0.0:
                    block_defence_game_over_timer = game_timer
                
                # Return to main menu after 3 seconds
                if game_timer - block_defence_game_over_timer >= 3.0:
                    start_screen = True
                    in_block_defence = False
                    block_defence_game_over_timer = 0.0
                    # Reset Block Defence coins when game over
                    block_defence_coins = 0

    # Wave completion timer logic
    if wave_completion_timer > 0:
        wave_completion_timer -= dt
        if wave_completion_timer < 0:
            wave_completion_timer = 0
            wave_completion_message = ""

    # Pause countdown timer logic
    if pause_countdown > 0:
        pause_countdown -= dt
        if pause_countdown < 0:
            pause_countdown = 0
            game_paused = False

    # Draw pause overlay and countdown
    if ((game_paused or pause_countdown > 0) and not console_open and not admin_code_open
            and not admin_panel_open and not pause_menu_open and not in_menu and not enemy_menu_open and not block_menu_open):
        # Draw semi-transparent black overlay (but not when shop is open)
        if True:
            pause_overlay = pygame.Surface((WIDTH, HEIGHT), pygame.SRCALPHA)
            pause_overlay.fill((0, 0, 0, 128))  # Black with 50% transparency
            screen.blit(pause_overlay, (0, 0))
        
        if game_paused and pause_countdown == 0:
            # Draw "PAUSED" text only if not in countdown and not in shop
            pause_text = font.render("PAUSED", True, WHITE)
            text_rect = pause_text.get_rect(center=(WIDTH // 2, HEIGHT // 2))
            screen.blit(pause_text, text_rect)
        elif pause_countdown > 0:
            # Each number flies in from the front, holds for most of its second, then shrinks away
            number = int(pause_countdown) + 1
            t = 1 - (pause_countdown - math.floor(pause_countdown))  # 0 -> 1 across this number's second
            if t < 0.22:
                zoom = t / 0.22
                scale = 4.2 - 3.2 * (1 - (1 - zoom) ** 3)  # Rushes in from close up, easing to a stop
                alpha = min(255, int(255 * t / 0.12))
            elif t < 0.78:
                scale = 1.0 - 0.06 * ((t - 0.22) / 0.56)  # Almost still, drifting back very slightly
                alpha = 255
            else:
                shrink = (t - 0.78) / 0.22
                scale = 0.94 * (1 - shrink ** 2) + 0.06   # Shrinks away as the next number arrives
                alpha = int(255 * (1 - shrink))
            digit = get_bubble_text(str(number), 120, (255, 245, 200), (255, 170, 40))
            scaled = pygame.transform.smoothscale(digit, (max(1, int(digit.get_width() * scale)),
                                                          max(1, int(digit.get_height() * scale))))
            scaled.set_alpha(max(0, min(255, alpha)))
            screen.blit(scaled, scaled.get_rect(center=(WIDTH // 2, HEIGHT // 2)))

    # Shooting Range play/editor toggle (bottom right). Pause is in the pause menu now (Escape).
    if in_shooting_range and not in_menu and not game_over:
        play_button = pygame.Rect(WIDTH - 120, HEIGHT - 60, 100, 40)
        play_color = GREEN if shooting_range_editor_mode else YELLOW
        draw_button(play_button, play_color)
        play_text = smaller_button_font.render("Play" if shooting_range_editor_mode else "Editor", True, BLACK)
        screen.blit(play_text, play_text.get_rect(center=play_button.center))

    # Update Coin Controller cooldown
    if coin_controller_cooldown > 0:
        coin_controller_cooldown -= dt
        if coin_controller_cooldown < 0:
            coin_controller_cooldown = 0

    # Triple Bullet timer/cooldown logic
    if triple_bullet_active:
        triple_bullet_timer += dt
        if triple_bullet_timer >= triple_bullet_duration:
            triple_bullet_active = False
            triple_bullet_timer = 0
    elif triple_bullet_cooldown > 0:
        triple_bullet_cooldown -= dt
        if triple_bullet_cooldown < 0:
            triple_bullet_cooldown = 0

    # Update Coin Controller attraction effect
    if coin_controller_active:
        coin_controller_timer += dt
        if coin_controller_timer >= coin_controller_duration:
            coin_controller_active = False
            # Start cooldown when duration expires
            coin_controller_cooldown = coin_controller_cooldown_time
        else:
            # Move all coins towards player
            player_center_x = player_x + player_size // 2
            player_center_y = player_y + player_size // 2
            for coin in coins:
                dx = player_center_x - coin['x']
                dy = player_center_y - coin['y']
                distance = math.hypot(dx, dy)
                if distance > 0:
                    # Normalize direction and apply speed
                    dx = (dx / distance) * coin_attraction_speed * dt
                    dy = (dy / distance) * coin_attraction_speed * dt
                    coin['x'] += dx
                    coin['y'] += dy
            
            # Check if all coins have been collected
            if len(coins) == 0:
                coin_controller_active = False
                coin_controller_cooldown = coin_controller_cooldown_time

    # Draw invincibility indicator if active (not over menus)
    if invincible and not in_menu:
        inv_text = button_font.render("INVINCIBLE", True, YELLOW)
        inv_y = 110 if (in_storm_survival or active_boss is not None) and not in_menu else 40  # Below the timer tab / boss bar
        if ability_badge_anim > 0.05 and not in_menu:
            inv_y += 80  # And below the ability badge when that is showing
        inv_rect = inv_text.get_rect(center=(WIDTH // 2, inv_y))
        blit_hud(inv_text, inv_rect)

    # Block Defence repair menu, sliding down into the middle
    block_hit_flash = max(0.0, block_hit_flash - dt)
    block_menu_anim += ((1.0 if block_menu_open else 0.0) - block_menu_anim) * min(1.0, dt * 12)
    if block_menu_anim > 0.02:
        draw_block_menu()

    # Sandbox Add Enemies menu, sliding down into the middle
    enemy_menu_anim += ((1.0 if enemy_menu_open else 0.0) - enemy_menu_anim) * min(1.0, dt * 12)
    if enemy_menu_anim > 0.02:
        draw_enemy_menu()

    # Pause menu, sliding down from the top
    pause_menu_anim += ((1.0 if pause_menu_open else 0.0) - pause_menu_anim) * min(1.0, dt * 12)
    if pause_menu_anim > 0.02:
        draw_pause_menu()

    # Code console bar (drops down from the top when you press `), then any admin screen on top
    console_anim = min(1.0, console_anim + dt * 6) if console_open else max(0.0, console_anim - dt * 8)
    if console_anim > 0.01:
        draw_console_bar()
    if admin_code_open:
        draw_admin_code()
    elif admin_panel_open:
        draw_admin_panel()

    # Code console feedback message
    if console_message_timer > 0:
        console_message_timer -= dt
        message_surface = button_font.render(console_message, True, WHITE)
        # Keep the toast clear of the console, and of menu headings/tabs at the top of the screen
        if admin_code_open or admin_panel_open:
            message_y = 200
        elif in_menu and not console_open:
            message_y = HEIGHT - 72  # Below the menu buttons
        else:
            message_y = 150
        message_rect = message_surface.get_rect(center=(WIDTH // 2, message_y))
        pygame.draw.rect(screen, (30, 30, 30), message_rect.inflate(30, 16), border_radius=10)
        screen.blit(message_surface, message_rect)

    pygame.display.flip()

pygame.quit()
sys.exit()
